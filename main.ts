// Lossless PNG re-encoder for the png-squeeze bounty.
// Reads /input/i001..i008/image.png (RGBA8, colour type 6) and writes a
// smaller lossless PNG for each to /output/<id>/image.png. MAKEFUN_INPUT_DIR /
// MAKEFUN_OUTPUT_DIR (or INPUT_DIR / OUTPUT_DIR) override the roots locally.
//
// Method: try every colour type that can represent the pixels exactly
// (palette in frequency and first-appearance order, grey, grey+alpha,
// RGB, RGBA). For each candidate, trial several deterministic scanline
// filter assignments (uniform filters and an entropy DP with a switch
// penalty), compress each stream with zlib level 9 / memLevel 8
// (default and Z_FILTERED where benchmarking shows the filtered
// strategy can win), and keep the smallest PNG. Finally the
// winning stream is recompressed with a pure-JS optimal-parse DEFLATE
// encoder (hash-chain LZ77 + bit-cost DP + iterated dynamic Huffman +
// block splitting); its output is verified by inflation and kept only
// when smaller. All choices are fixed and deterministic.

const fs = require('node:fs');
const path = require('node:path');
const zlib = require('node:zlib');

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR || process.env.INPUT_DIR || '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR || process.env.OUTPUT_DIR || '/output';
const IMAGE_COUNT = 8;
const PNG_SIGNATURE = Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]);

// ---------------------------------------------------------------------------
// CRC32 (PNG polynomial), table generated once at startup.
// ---------------------------------------------------------------------------
const CRC_TABLE = new Uint32Array(256);
for (let n = 0; n < 256; n++) {
  let c = n;
  for (let k = 0; k < 8; k++) {
    c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
  }
  CRC_TABLE[n] = c >>> 0;
}

function crc32(buf) {
  let c = 0xffffffff;
  for (let i = 0; i < buf.length; i++) {
    c = CRC_TABLE[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
  }
  return (c ^ 0xffffffff) >>> 0;
}

function makeChunk(type, data) {
  const chunk = Buffer.alloc(12 + data.length);
  chunk.writeUInt32BE(data.length, 0);
  chunk.write(type, 4, 'ascii');
  data.copy(chunk, 8);
  chunk.writeUInt32BE(crc32(chunk.subarray(4, 8 + data.length)), 8 + data.length);
  return chunk;
}

// ---------------------------------------------------------------------------
// PNG decoding for the fixed input format: bit depth 8, colour type 6,
// non-interlaced. All five scanline filters are implemented.
// ---------------------------------------------------------------------------
function paethPredictor(left, up, upLeft) {
  const p = left + up - upLeft;
  const pa = Math.abs(p - left);
  const pb = Math.abs(p - up);
  const pc = Math.abs(p - upLeft);
  if (pa <= pb && pa <= pc) return left;
  if (pb <= pc) return up;
  return upLeft;
}

function decodePng(buf) {
  for (let i = 0; i < 8; i++) {
    if (buf[i] !== PNG_SIGNATURE[i]) throw new Error('input is not a PNG');
  }
  let width = 0;
  let height = 0;
  const idatParts = [];
  let offset = 8;
  while (offset + 8 <= buf.length) {
    const length = buf.readUInt32BE(offset);
    const type = buf.toString('ascii', offset + 4, offset + 8);
    const data = buf.subarray(offset + 8, offset + 8 + length);
    if (type === 'IHDR') {
      width = data.readUInt32BE(0);
      height = data.readUInt32BE(4);
      const bitDepth = data[8];
      const colorType = data[9];
      const compression = data[10];
      const filterMethod = data[11];
      const interlace = data[12];
      if (bitDepth !== 8 || colorType !== 6 || compression !== 0 || filterMethod !== 0 || interlace !== 0) {
        throw new Error('unsupported input PNG format');
      }
    } else if (type === 'IDAT') {
      idatParts.push(data);
    } else if (type === 'IEND') {
      break;
    }
    offset += 12 + length;
  }
  if (width === 0 || height === 0 || idatParts.length === 0) {
    throw new Error('incomplete input PNG');
  }

  const inflated = zlib.inflateSync(Buffer.concat(idatParts));
  const stride = width * 4;
  if (inflated.length < height * (stride + 1)) {
    throw new Error('truncated PNG image data');
  }
  const pixels = new Uint8Array(stride * height);
  for (let y = 0; y < height; y++) {
    const filter = inflated[y * (stride + 1)];
    const rowIn = y * (stride + 1) + 1;
    const rowOut = y * stride;
    const prevOut = rowOut - stride;
    for (let i = 0; i < stride; i++) {
      const value = inflated[rowIn + i];
      const left = i >= 4 ? pixels[rowOut + i - 4] : 0;
      const up = y > 0 ? pixels[prevOut + i] : 0;
      const upLeft = y > 0 && i >= 4 ? pixels[prevOut + i - 4] : 0;
      let predictor = 0;
      if (filter === 1) predictor = left;
      else if (filter === 2) predictor = up;
      else if (filter === 3) predictor = (left + up) >> 1;
      else if (filter === 4) predictor = paethPredictor(left, up, upLeft);
      else if (filter !== 0) throw new Error('unknown PNG filter type');
      pixels[rowOut + i] = (value + predictor) & 0xff;
    }
  }
  return { width, height, pixels };
}

// ---------------------------------------------------------------------------
// Image analysis: palette eligibility and the structural facts that decide
// which colour types can represent the pixels losslessly. The counts map
// preserves insertion order, which is first-appearance order.
// ---------------------------------------------------------------------------
function analyseImage(pixels) {
  let counts = new Map();
  let palettePossible = true;
  let allOpaque = true;
  let allGrey = true;
  let alphaBinary = true;
  let hasTransparent = false;
  let transparentUniform = true;
  let transparentRgb = -1;

  for (let i = 0; i < pixels.length; i += 4) {
    const r = pixels[i];
    const g = pixels[i + 1];
    const b = pixels[i + 2];
    const a = pixels[i + 3];
    if (a !== 255) allOpaque = false;
    if (r !== g || g !== b) allGrey = false;
    if (a !== 0 && a !== 255) alphaBinary = false;
    if (a === 0) {
      hasTransparent = true;
      const rgb = (r << 16) | (g << 8) | b;
      if (transparentRgb === -1) transparentRgb = rgb;
      else if (rgb !== transparentRgb) transparentUniform = false;
    }
    if (palettePossible) {
      const key = ((r << 24) | (g << 16) | (b << 8) | a) >>> 0;
      const existing = counts.get(key);
      if (existing === undefined) {
        if (counts.size >= 256) {
          palettePossible = false;
          counts = null;
        } else {
          counts.set(key, 1);
        }
      } else {
        counts.set(key, existing + 1);
      }
    }
  }

  let rgbTrnsOk = false;
  if (alphaBinary && hasTransparent && transparentUniform) {
    rgbTrnsOk = true;
    for (let i = 0; i < pixels.length; i += 4) {
      if (pixels[i + 3] === 255 && ((pixels[i] << 16) | (pixels[i + 1] << 8) | pixels[i + 2]) === transparentRgb) {
        rgbTrnsOk = false;
        break;
      }
    }
  }

  return { counts, allOpaque, allGrey, rgbTrnsOk, transparentRgb };
}

// ---------------------------------------------------------------------------
// Candidate encodings. Each candidate carries its unfiltered scanline bytes
// (no filter bytes) plus the PLTE/tRNS payloads it needs, if any. Palette
// candidates are built in two orderings: frequency-descending and
// first-appearance.
// ---------------------------------------------------------------------------
function makePaletteCandidate(image, entries) {
  const { width, height, pixels } = image;
  const plte = Buffer.alloc(entries.length * 3);
  const alphas = new Array(entries.length);
  const indexOf = new Map();
  for (let idx = 0; idx < entries.length; idx++) {
    const key = entries[idx][0];
    indexOf.set(key, idx);
    plte[idx * 3] = (key >>> 24) & 0xff;
    plte[idx * 3 + 1] = (key >>> 16) & 0xff;
    plte[idx * 3 + 2] = (key >>> 8) & 0xff;
    alphas[idx] = key & 0xff;
  }
  let lastAlpha = alphas.length - 1;
  while (lastAlpha >= 0 && alphas[lastAlpha] === 255) lastAlpha--;
  const trns = lastAlpha >= 0 ? Buffer.from(alphas.slice(0, lastAlpha + 1)) : null;
  const raw = new Uint8Array(width * height);
  for (let p = 0, i = 0; i < pixels.length; i += 4, p++) {
    raw[p] = indexOf.get(((pixels[i] << 24) | (pixels[i + 1] << 16) | (pixels[i + 2] << 8) | pixels[i + 3]) >>> 0);
  }
  return { colorType: 3, bpp: 1, raw, plte, trns, palette: true };
}

function buildCandidates(image, info) {
  const { width, height, pixels } = image;
  const pixelCount = width * height;
  const candidates = [];

  if (info.counts !== null) {
    const firstAppearance = Array.from(info.counts.entries());
    const frequency = firstAppearance.slice().sort((a, b) => b[1] - a[1] || a[0] - b[0]);
    candidates.push(makePaletteCandidate(image, frequency));
    let sameOrder = true;
    for (let k = 0; k < frequency.length; k++) {
      if (frequency[k][0] !== firstAppearance[k][0]) { sameOrder = false; break; }
    }
    if (!sameOrder) candidates.push(makePaletteCandidate(image, firstAppearance));
  }

  const paletteCount = info.counts === null ? Infinity : info.counts.size;

  if (info.allGrey && info.allOpaque) {
    const raw = new Uint8Array(pixelCount);
    for (let p = 0, i = 0; i < pixels.length; i += 4, p++) raw[p] = pixels[i];
    candidates.push({ colorType: 0, bpp: 1, raw, plte: null, trns: null, palette: false });
  }

  if (info.allGrey && !info.allOpaque) {
    if (info.rgbTrnsOk) {
      const raw = new Uint8Array(pixelCount);
      for (let p = 0, i = 0; i < pixels.length; i += 4, p++) raw[p] = pixels[i];
      const trns = Buffer.alloc(2);
      trns.writeUInt16BE(info.transparentRgb & 0xff, 0);
      candidates.push({ colorType: 0, bpp: 1, raw, plte: null, trns, palette: false });
    } else {
      const raw = new Uint8Array(pixelCount * 2);
      for (let p = 0, i = 0; i < pixels.length; i += 4, p += 2) {
        raw[p] = pixels[i];
        raw[p + 1] = pixels[i + 3];
      }
      candidates.push({ colorType: 4, bpp: 2, raw, plte: null, trns: null, palette: false });
    }
  }

  if (!info.allGrey && (info.allOpaque || info.rgbTrnsOk) && paletteCount > 48) {
    const raw = new Uint8Array(pixelCount * 3);
    for (let p = 0, i = 0; i < pixels.length; i += 4, p += 3) {
      raw[p] = pixels[i];
      raw[p + 1] = pixels[i + 1];
      raw[p + 2] = pixels[i + 2];
    }
    if (info.allOpaque) {
      candidates.push({ colorType: 2, bpp: 3, raw, plte: null, trns: null, palette: false });
    } else {
      const trns = Buffer.alloc(6);
      trns.writeUInt16BE((info.transparentRgb >> 16) & 0xff, 0);
      trns.writeUInt16BE((info.transparentRgb >> 8) & 0xff, 2);
      trns.writeUInt16BE(info.transparentRgb & 0xff, 4);
      candidates.push({ colorType: 2, bpp: 3, raw, plte: null, trns, palette: false });
    }
  }

  if (!info.allGrey && !info.allOpaque && !info.rgbTrnsOk && paletteCount > 96) {
    candidates.push({ colorType: 6, bpp: 4, raw: pixels, plte: null, trns: null, palette: false });
  }
  return candidates;
}

// ---------------------------------------------------------------------------
// Scanline filtering. One pass computes, per row and filter, the
// byte-entropy cost, and caches the filtered row bytes for every
// (row, filter) pair so trial streams are assembled by copying rows.
// ---------------------------------------------------------------------------
function computeRowCostsAndCache(raw, width, height, bpp) {
  const stride = width * bpp;
  const entropy = new Float64Array(height * 5);
  const cache = new Uint8Array(height * 5 * stride);
  const histograms = new Uint32Array(5 * 256);
  const strideLog = Math.log2(stride);
  for (let y = 0; y < height; y++) {
    histograms.fill(0);
    const rowStart = y * stride;
    const prevStart = y > 0 ? rowStart - stride : -1;
    const cacheRow = y * 5 * stride;
    for (let i = 0; i < stride; i++) {
      const value = raw[rowStart + i];
      const left = i >= bpp ? raw[rowStart + i - bpp] : 0;
      const up = prevStart >= 0 ? raw[prevStart + i] : 0;
      const upLeft = prevStart >= 0 && i >= bpp ? raw[prevStart + i - bpp] : 0;
      const d0 = value;
      const d1 = (value - left) & 0xff;
      const d2 = (value - up) & 0xff;
      const d3 = (value - ((left + up) >> 1)) & 0xff;
      const d4 = (value - paethPredictor(left, up, upLeft)) & 0xff;
      cache[cacheRow + i] = d0;
      cache[cacheRow + stride + i] = d1;
      cache[cacheRow + 2 * stride + i] = d2;
      cache[cacheRow + 3 * stride + i] = d3;
      cache[cacheRow + 4 * stride + i] = d4;
      histograms[d0]++;
      histograms[256 + d1]++;
      histograms[512 + d2]++;
      histograms[768 + d3]++;
      histograms[1024 + d4]++;
    }
    for (let f = 0; f < 5; f++) {
      let weighted = 0;
      const base = f * 256;
      for (let v = 0; v < 256; v++) {
        const count = histograms[base + v];
        if (count > 1) weighted += count * Math.log2(count);
      }
      entropy[y * 5 + f] = stride * strideLog - weighted;
    }
  }
  return { entropy, cache, stride };
}

function dpFilters(cost, height, switchPenalty) {
  let previous = new Float64Array(5);
  for (let f = 0; f < 5; f++) previous[f] = cost[f];
  const back = new Uint8Array(height * 5);
  for (let y = 1; y < height; y++) {
    const current = new Float64Array(5);
    for (let f = 0; f < 5; f++) {
      let best = Infinity;
      let bestPrev = 0;
      for (let pf = 0; pf < 5; pf++) {
        const value = previous[pf] + (pf === f ? 0 : switchPenalty);
        if (value < best) {
          best = value;
          bestPrev = pf;
        }
      }
      current[f] = best + cost[y * 5 + f];
      back[y * 5 + f] = bestPrev;
    }
    previous = current;
  }
  const filters = new Uint8Array(height);
  let chosen = 0;
  let best = Infinity;
  for (let f = 0; f < 5; f++) {
    if (previous[f] < best) {
      best = previous[f];
      chosen = f;
    }
  }
  for (let y = height - 1; y >= 0; y--) {
    filters[y] = chosen;
    chosen = back[y * 5 + chosen];
  }
  return filters;
}

function fixedFilters(height, filter) {
  return new Uint8Array(height).fill(filter);
}

function buildFilteredStream(prep, height, filters) {
  const stride = prep.stride;
  const out = new Uint8Array(height * (stride + 1));
  for (let y = 0; y < height; y++) {
    const outStart = y * (stride + 1);
    out[outStart] = filters[y];
    out.set(prep.cache.subarray((y * 5 + filters[y]) * stride, (y * 5 + filters[y] + 1) * stride), outStart + 1);
  }
  return out;
}

// ---------------------------------------------------------------------------
// PNG assembly and candidate evaluation with zlib trials.
// ---------------------------------------------------------------------------
function assemblePng(width, height, candidate, compressed) {
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(width, 0);
  ihdr.writeUInt32BE(height, 4);
  ihdr[8] = 8;
  ihdr[9] = candidate.colorType;
  ihdr[10] = 0;
  ihdr[11] = 0;
  ihdr[12] = 0;
  const parts = [PNG_SIGNATURE, makeChunk('IHDR', ihdr)];
  if (candidate.plte !== null) parts.push(makeChunk('PLTE', candidate.plte));
  if (candidate.trns !== null) parts.push(makeChunk('tRNS', candidate.trns));
  parts.push(makeChunk('IDAT', compressed));
  parts.push(makeChunk('IEND', Buffer.alloc(0)));
  return Buffer.concat(parts);
}

function streamDefsFor(image, candidate, prep) {
  const height = image.height;
  let defs;
  if (candidate.palette) {
    // Palette indices are categorical: adaptive and Up/Average/Paeth
    // filter choices never win on benchmark data, so palette trials use
    // the uniform None and Sub streams only.
    defs = [
      { filters: fixedFilters(height, 0), filtered: false },
      { filters: fixedFilters(height, 1), filtered: false },
    ];
  } else {
    // Z_FILTERED is trialled on the Paeth and adaptive streams, where
    // benchmarking shows it can win; on uniform None/Up streams it
    // consistently loses to the default strategy. The uniform Sub
    // stream and the per-row adaptive choices never won on benchmark
    // data (Paeth and the entropy DP cover their cases), so the trial
    // set is the uniform None/Up/Paeth streams plus the entropy DP.
    // The fixed-Paeth stream is always trialled, so the fixed-Paeth
    // floor candidate is always evaluated.
    defs = [
      { filters: fixedFilters(height, 0), filtered: false },
      { filters: fixedFilters(height, 2), filtered: false },
      { filters: fixedFilters(height, 4), filtered: true },
      { filters: dpFilters(prep.entropy, height, 128), filtered: true },
    ];
  }
  // Merge duplicate filter assignments, keeping the union of strategies.
  const merged = [];
  for (const def of defs) {
    let found = null;
    for (const m of merged) {
      let same = true;
      for (let y = 0; y < height; y++) {
        if (m.filters[y] !== def.filters[y]) { same = false; break; }
      }
      if (same) { found = m; break; }
    }
    if (found !== null) found.filtered = found.filtered || def.filtered;
    else merged.push({ filters: def.filters, filtered: def.filtered });
  }
  return merged;
}

function evaluateDefs(image, candidate, prep, defs) {
  // Default-strategy trials for every stream first; Z_FILTERED trials
  // follow for the streams where it can win (Paeth/adaptive streams whose
  // default result is within 4% of the best default result — benchmarking
  // shows the filtered strategy gains at most ~2.5% on a stream, so a
  // stream further behind cannot overtake the leader through it).
  let bestPng = null;
  let bestStream = null;
  const evaluated = [];
  for (const def of defs) {
    const stream = buildFilteredStream(prep, image.height, def.filters);
    const png = assemblePng(image.width, image.height, candidate, zlib.deflateSync(stream, { level: 9, memLevel: 8 }));
    evaluated.push({ def, stream, pngLength: png.length });
    if (bestPng === null || png.length < bestPng.length) {
      bestPng = png;
      bestStream = stream;
    }
  }
  const bestDefaultLength = bestPng.length;
  for (const ev of evaluated) {
    if (!ev.def.filtered) continue;
    if (ev.pngLength > bestDefaultLength * 1.04) continue;
    const png = assemblePng(image.width, image.height, candidate, zlib.deflateSync(ev.stream, { level: 9, memLevel: 8, strategy: zlib.constants.Z_FILTERED }));
    if (png.length < bestPng.length) {
      bestPng = png;
      bestStream = ev.stream;
    }
  }
  return { png: bestPng, stream: bestStream };
}

// ---------------------------------------------------------------------------
// Optimal-parse DEFLATE encoder (pure JS, deterministic).
// LZ77 matches come from hash chains over 3-byte sequences; for each
// position the search records, per match length, the closest distance
// achieving it. A forward dynamic program then chooses literals and
// matches minimising total bit cost under dynamic Huffman code lengths,
// iterating parse -> symbol counts -> length-limited Huffman lengths.
// Blocks are split where per-block Huffman tables pay for their headers,
// and each block is re-parsed under its own code lengths when the stream
// is small enough for that to be cheap. The emitted zlib stream is
// verified by inflation before use.
// ---------------------------------------------------------------------------
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const LEN_CODE_OF_LEN = new Uint16Array(259);
const LEN_EXTRA_BITS = new Uint8Array(259);
for (let c = 0; c < 29; c++) {
  const base = LEN_BASE[c];
  const extra = LEN_EXTRA[c];
  const count = c === 28 ? 1 : (1 << extra);
  for (let k = 0; k < count; k++) {
    LEN_CODE_OF_LEN[base + k] = 257 + c;
    LEN_EXTRA_BITS[base + k] = extra;
  }
}
const DIST_CODE_OF_DIST = new Uint8Array(32769);
const DIST_EXTRA_BITS = new Uint8Array(32769);
for (let c = 0; c < 30; c++) {
  const base = DIST_BASE[c];
  const extra = DIST_EXTRA[c];
  const count = 1 << extra;
  for (let k = 0; k < count && base + k <= 32768; k++) {
    DIST_CODE_OF_DIST[base + k] = c;
    DIST_EXTRA_BITS[base + k] = extra;
  }
}
const RANGE_MAXIMA = [];
for (let c = 0; c < 29; c++) RANGE_MAXIMA.push(LEN_BASE[c] + (c === 28 ? 0 : (1 << LEN_EXTRA[c]) - 1));
const DP_LENGTH_CAP = 12;

// Length-limited Huffman code lengths via package-merge. Ties break by
// symbol index, so the result is deterministic.
function huffmanLengths(freq, maxLen) {
  const n = freq.length;
  const lens = new Uint8Array(n);
  const syms = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) syms.push(i);
  if (syms.length === 0) return lens;
  if (syms.length === 1) {
    lens[syms[0]] = 1;
    return lens;
  }
  let list = syms.map((s) => ({ w: freq[s], s: [s] }));
  list.sort((a, b) => a.w - b.w || a.s[0] - b.s[0]);
  const leafList = list;
  for (let level = 1; level < maxLen; level++) {
    const packaged = [];
    for (let i = 0; i + 1 < list.length; i += 2) {
      packaged.push({ w: list[i].w + list[i + 1].w, s: list[i].s.concat(list[i + 1].s) });
    }
    const merged = [];
    let a = 0;
    let b = 0;
    while (a < leafList.length && b < packaged.length) {
      if (leafList[a].w <= packaged[b].w) merged.push(leafList[a++]);
      else merged.push(packaged[b++]);
    }
    while (a < leafList.length) merged.push(leafList[a++]);
    while (b < packaged.length) merged.push(packaged[b++]);
    list = merged;
  }
  const need = 2 * syms.length - 2;
  for (let i = 0; i < need && i < list.length; i++) {
    const ss = list[i].s;
    for (let k = 0; k < ss.length; k++) lens[ss[k]]++;
  }
  return lens;
}

function canonicalCodes(lens) {
  const blCount = new Uint32Array(16);
  for (let i = 0; i < lens.length; i++) blCount[lens[i]]++;
  blCount[0] = 0;
  const nextCode = new Uint32Array(16);
  let code = 0;
  for (let bits = 1; bits <= 15; bits++) {
    code = (code + blCount[bits - 1]) << 1;
    nextCode[bits] = code;
  }
  const codes = new Uint32Array(lens.length);
  for (let i = 0; i < lens.length; i++) {
    if (lens[i] > 0) codes[i] = nextCode[lens[i]]++;
  }
  return codes;
}

function findMatches(data) {
  const N = data.length;
  const matchMax = new Uint16Array(N);
  const bpIndex = new Int32Array(N).fill(-1);
  const bpSegCount = new Uint8Array(N);
  let bpCap = 1 << 16;
  let bpLenFrom = new Uint16Array(bpCap);
  let bpDist = new Uint32Array(bpCap);
  let bpCount = 0;
  const HASH_MASK = 262143;
  const head = new Int32Array(262144).fill(-1);
  const prev = new Int32Array(N).fill(-1);
  // 4-byte little-endian words at every offset, for fast match extension.
  const words = new Uint32Array(N + 4);
  for (let i = 0; i + 3 < N; i++) {
    words[i] = (data[i] | (data[i + 1] << 8) | (data[i + 2] << 16) | (data[i + 3] << 24)) >>> 0;
  }
  for (let i = 0; i < N; i++) {
    if (i + 2 >= N) break;
    const h = ((((data[i] << 16) ^ (data[i + 1] << 8) ^ data[i + 2]) * 0x9e3779b1) >>> 14) & HASH_MASK;
    let cand = head[h];
    let bestLen = 0;
    // After a long match at the previous position, a near-best match
    // here is found within the first few candidates; cap the chain.
    let chainLimit = i > 0 && matchMax[i - 1] >= 64 ? 48 : 224;
    let steps = 0;
    const maxLen = Math.min(258, N - i);
    while (cand >= 0 && steps < chainLimit) {
      const dist = i - cand;
      if (dist > 32768) break;
      if (bestLen === 0 || (data[cand + bestLen] === data[i + bestLen] && data[cand + bestLen - 1] === data[i + bestLen - 1])) {
        let len = 0;
        while (len + 4 <= maxLen && words[cand + len] === words[i + len]) len += 4;
        while (len < maxLen && data[cand + len] === data[i + len]) len++;
        if (len >= 3 && len > bestLen) {
          if (bpIndex[i] < 0) bpIndex[i] = bpCount;
          if (bpCount === bpCap) {
            bpCap *= 2;
            const nl = new Uint16Array(bpCap);
            nl.set(bpLenFrom);
            bpLenFrom = nl;
            const nd = new Uint32Array(bpCap);
            nd.set(bpDist);
            bpDist = nd;
          }
          bpLenFrom[bpCount] = bestLen + 1 < 3 ? 3 : bestLen + 1;
          bpDist[bpCount] = dist;
          bpCount++;
          bpSegCount[i]++;
          bestLen = len;
          if (bestLen >= 258) break;
          if (bestLen >= 32) chainLimit = Math.min(chainLimit, 64);
          else if (bestLen >= 16) chainLimit = Math.min(chainLimit, 128);
        }
      }
      cand = prev[cand];
      steps++;
    }
    matchMax[i] = bestLen;
    prev[i] = head[h];
    head[h] = i;
  }
  return { matchMax, bpIndex, bpSegCount, bpLenFrom, bpDist };
}

function dpParse(data, matches, litCost, lenCost, distCost, start, end, dp, backPrev, backLen, backDist, lengthCap) {
  const matchMax = matches.matchMax;
  const bpIndex = matches.bpIndex;
  const bpSegCount = matches.bpSegCount;
  const bpLenFrom = matches.bpLenFrom;
  const bpDist = matches.bpDist;
  for (let i = start; i <= end; i++) dp[i] = Infinity;
  dp[start] = 0;
  for (let i = start; i < end; i++) {
    const base = dp[i];
    if (base === Infinity) continue;
    const litTotal = base + litCost[data[i]];
    if (litTotal < dp[i + 1]) {
      dp[i + 1] = litTotal;
      backPrev[i + 1] = i;
      backLen[i + 1] = 1;
      backDist[i + 1] = 0;
    }
    let L = matchMax[i];
    if (L < 3) continue;
    if (L > end - i) L = end - i;
    if (L < 3) continue;
    const seg0 = bpIndex[i];
    const segN = bpSegCount[i];
    let seg = 0;
    while (seg + 1 < segN && bpLenFrom[seg0 + seg + 1] <= 3) seg++;
    let dist = bpDist[seg0 + seg];
    let segBase = base + distCost[dist];
    const cap = Math.min(L, lengthCap);
    for (let len = 3; len <= cap; len++) {
      while (seg + 1 < segN && bpLenFrom[seg0 + seg + 1] <= len) {
        seg++;
        dist = bpDist[seg0 + seg];
        segBase = base + distCost[dist];
      }
      const total = segBase + lenCost[len];
      const j = i + len;
      if (total < dp[j]) {
        dp[j] = total;
        backPrev[j] = i;
        backLen[j] = len;
        backDist[j] = dist;
      }
    }
    if (L > lengthCap) {
      for (let r = 0; r < RANGE_MAXIMA.length; r++) {
        const len = RANGE_MAXIMA[r];
        if (len <= lengthCap || len > L) continue;
        while (seg + 1 < segN && bpLenFrom[seg0 + seg + 1] <= len) {
          seg++;
          dist = bpDist[seg0 + seg];
          segBase = base + distCost[dist];
        }
        const total = segBase + lenCost[len];
        const j = i + len;
        if (total < dp[j]) {
          dp[j] = total;
          backPrev[j] = i;
          backLen[j] = len;
          backDist[j] = dist;
        }
      }
      while (seg + 1 < segN && bpLenFrom[seg0 + seg + 1] <= L) {
        seg++;
        dist = bpDist[seg0 + seg];
        segBase = base + distCost[dist];
      }
      const total = segBase + lenCost[L];
      const j = i + L;
      if (total < dp[j]) {
        dp[j] = total;
        backPrev[j] = i;
        backLen[j] = L;
        backDist[j] = dist;
      }
    }
  }
}

function collectSymbols(backPrev, backLen, backDist, start, end) {
  const rev = [];
  let pos = end;
  while (pos > start) {
    const p = backPrev[pos];
    rev.push({ pos: p, len: backLen[pos], dist: backDist[pos] });
    pos = p;
  }
  rev.reverse();
  return rev;
}

function symbolCounts(data, syms, s0, s1) {
  const litFreq = new Float64Array(288);
  const distFreq = new Float64Array(32);
  for (let i = s0; i < s1; i++) {
    const s = syms[i];
    if (s.len === 1) litFreq[data[s.pos]]++;
    else {
      litFreq[LEN_CODE_OF_LEN[s.len]]++;
      distFreq[DIST_CODE_OF_DIST[s.dist]]++;
    }
  }
  litFreq[256]++;
  return { litFreq, distFreq };
}

function costsFromLengths(litLens, distLens) {
  const litCost = new Float64Array(288);
  for (let i = 0; i < 288; i++) litCost[i] = litLens[i] > 0 ? litLens[i] : 32;
  const lenCost = new Float64Array(259);
  for (let len = 3; len <= 258; len++) lenCost[len] = litCost[LEN_CODE_OF_LEN[len]] + LEN_EXTRA_BITS[len];
  const distCost = new Float64Array(32769);
  for (let d = 1; d <= 32768; d++) {
    const c = DIST_CODE_OF_DIST[d];
    distCost[d] = (distLens[c] > 0 ? distLens[c] : 32) + DIST_EXTRA_BITS[d];
  }
  return { litCost, lenCost, distCost };
}

function headerSequence(litLens, distLens) {
  const all = [];
  for (let i = 0; i < litLens.length; i++) all.push(litLens[i]);
  for (let i = 0; i < distLens.length; i++) all.push(distLens[i]);
  const seq = [];
  let i = 0;
  while (i < all.length) {
    const v = all[i];
    let run = 1;
    while (i + run < all.length && all[i + run] === v) run++;
    if (v === 0) {
      let r = run;
      while (r >= 11) {
        const take = Math.min(r, 138);
        seq.push({ sym: 18, extra: take - 11, extraBits: 7 });
        r -= take;
      }
      if (r >= 3) {
        seq.push({ sym: 17, extra: r - 3, extraBits: 3 });
        r = 0;
      }
      while (r > 0) {
        seq.push({ sym: 0, extra: 0, extraBits: 0 });
        r--;
      }
    } else {
      seq.push({ sym: v, extra: 0, extraBits: 0 });
      let r = run - 1;
      while (r >= 3) {
        const take = Math.min(r, 6);
        seq.push({ sym: 16, extra: take - 3, extraBits: 2 });
        r -= take;
      }
      while (r > 0) {
        seq.push({ sym: v, extra: 0, extraBits: 0 });
        r--;
      }
    }
    i += run;
  }
  return seq;
}

const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

function headerBitsAndLens(litLens, distLens) {
  const seq = headerSequence(litLens, distLens);
  const freq = new Float64Array(19);
  let extraBits = 0;
  for (const s of seq) {
    freq[s.sym]++;
    extraBits += s.extraBits;
  }
  const clLens = huffmanLengths(freq, 7);
  let nz = 0;
  let used = -1;
  for (let i = 0; i < 19; i++) {
    if (freq[i] > 0) {
      nz++;
      used = i;
    }
  }
  if (nz === 1) clLens[used === 0 ? 1 : 0] = 1;
  let hclenCount = 19;
  while (hclenCount > 4 && clLens[CL_ORDER[hclenCount - 1]] === 0) hclenCount--;
  let bits = 3 + 5 + 5 + 4 + 3 * hclenCount + extraBits;
  for (const s of seq) bits += clLens[s.sym];
  return { seq, clLens, hclenCount, bits };
}

function blockCostEstimate(litFreq, distFreq) {
  const litLens = huffmanLengths(litFreq, 15);
  const distLens = huffmanLengths(distFreq, 15);
  let hdist = 32;
  while (hdist > 1 && distLens[hdist - 1] === 0) hdist--;
  let hlit = 288;
  while (hlit > 257 && litLens[hlit - 1] === 0) hlit--;
  const hdr = headerBitsAndLens(litLens.subarray(0, hlit), distLens.subarray(0, hdist));
  let bits = hdr.bits;
  for (let i = 0; i < 288; i++) bits += litFreq[i] * litLens[i];
  for (let i = 0; i < 32; i++) bits += distFreq[i] * distLens[i];
  return bits;
}

function reversedCodes(codes, lens) {
  const rev = new Uint32Array(codes.length);
  for (let i = 0; i < codes.length; i++) {
    const len = lens[i];
    if (len === 0) continue;
    let r = 0;
    const code = codes[i];
    for (let k = 0; k < len; k++) r = (r << 1) | ((code >>> k) & 1);
    rev[i] = r;
  }
  return rev;
}

class BitWriter {
  constructor() {
    this.bytes = [];
    this.bitBuf = 0;
    this.bitLen = 0;
  }
  writeBits(value, count) {
    this.bitBuf |= value << this.bitLen;
    this.bitLen += count;
    while (this.bitLen >= 8) {
      this.bytes.push(this.bitBuf & 0xff);
      this.bitBuf >>>= 8;
      this.bitLen -= 8;
    }
  }
  finish() {
    if (this.bitLen > 0) {
      this.bytes.push(this.bitBuf & 0xff);
      this.bitBuf = 0;
      this.bitLen = 0;
    }
    return Buffer.from(this.bytes);
  }
}

function emitBlock(bw, data, syms, s0, s1, isFinal) {
  const counts = symbolCounts(data, syms, s0, s1);
  const litLens = huffmanLengths(counts.litFreq, 15);
  const distLens = huffmanLengths(counts.distFreq, 15);
  let nzDist = 0;
  let usedDist = -1;
  for (let i = 0; i < 32; i++) {
    if (counts.distFreq[i] > 0) {
      nzDist++;
      usedDist = i;
    }
  }
  if (nzDist === 0) distLens[0] = 1;
  else if (nzDist === 1) distLens[usedDist === 0 ? 1 : 0] = 1;
  let hdist = 32;
  while (hdist > 1 && distLens[hdist - 1] === 0) hdist--;
  let hlit = 288;
  while (hlit > 257 && litLens[hlit - 1] === 0) hlit--;
  const hdr = headerBitsAndLens(litLens.subarray(0, hlit), distLens.subarray(0, hdist));
  const litCodes = canonicalCodes(litLens);
  const distCodes = canonicalCodes(distLens);
  const clCodes = canonicalCodes(hdr.clLens);
  const litRev = reversedCodes(litCodes, litLens);
  const distRev = reversedCodes(distCodes, distLens);
  const clRev = reversedCodes(clCodes, hdr.clLens);
  bw.writeBits(isFinal ? 1 : 0, 1);
  bw.writeBits(2, 2);
  bw.writeBits(hlit - 257, 5);
  bw.writeBits(hdist - 1, 5);
  bw.writeBits(hdr.hclenCount - 4, 4);
  for (let i = 0; i < hdr.hclenCount; i++) bw.writeBits(hdr.clLens[CL_ORDER[i]], 3);
  for (const s of hdr.seq) {
    bw.writeBits(clRev[s.sym], hdr.clLens[s.sym]);
    if (s.extraBits > 0) bw.writeBits(s.extra, s.extraBits);
  }
  for (let i = s0; i < s1; i++) {
    const s = syms[i];
    if (s.len === 1) {
      const b = data[s.pos];
      bw.writeBits(litRev[b], litLens[b]);
    } else {
      const lc = LEN_CODE_OF_LEN[s.len];
      bw.writeBits(litRev[lc], litLens[lc]);
      const leb = LEN_EXTRA_BITS[s.len];
      if (leb > 0) bw.writeBits(s.len - LEN_BASE[lc - 257], leb);
      const dc = DIST_CODE_OF_DIST[s.dist];
      bw.writeBits(distRev[dc], distLens[dc]);
      const deb = DIST_EXTRA_BITS[s.dist];
      if (deb > 0) bw.writeBits(s.dist - DIST_BASE[dc], deb);
    }
  }
  bw.writeBits(litRev[256], litLens[256]);
}

function adler32(data) {
  let a = 1;
  let b = 0;
  for (let i = 0; i < data.length; i++) {
    a = (a + data[i]) % 65521;
    b = (b + a) % 65521;
  }
  return ((b << 16) | a) >>> 0;
}

function emitZlibStream(data, syms, boundaries) {
  const bw = new BitWriter();
  for (let b = 0; b < boundaries.length - 1; b++) {
    emitBlock(bw, data, syms, boundaries[b], boundaries[b + 1], b === boundaries.length - 2);
  }
  const body = bw.finish();
  const out = Buffer.alloc(2 + body.length + 4);
  out[0] = 0x78;
  out[1] = 0xda;
  body.copy(out, 2);
  out.writeUInt32BE(adler32(data), 2 + body.length);
  return out;
}

// One parse path: iterate DP under costs seeded from `initCosts`, split
// into blocks, optionally re-parse per block, and return the smallest
// emitted stream among the single-block, split, and re-parsed variants.
function optimalParsePath(data, matches, work, initCosts, allowReparse) {
  const N = data.length;
  const dp = work.dp;
  const backPrev = work.backPrev;
  const backLen = work.backLen;
  const backDist = work.backDist;
  let costs = initCosts;
  let syms = null;
  for (let it = 0; it < 2; it++) {
    dpParse(data, matches, costs.litCost, costs.lenCost, costs.distCost, 0, N, dp, backPrev, backLen, backDist, it === 0 ? 8 : DP_LENGTH_CAP);
    syms = collectSymbols(backPrev, backLen, backDist, 0, N);
    const counts = symbolCounts(data, syms, 0, syms.length);
    costs = costsFromLengths(huffmanLengths(counts.litFreq, 15), huffmanLengths(counts.distFreq, 15));
  }
  const S = syms.length;
  // Prefix symbol counts at checkpoints, for block-split cost estimates.
  const CK = 2048;
  const nCk = Math.floor(S / CK) + 1;
  const ckLit = [];
  const ckDist = [];
  {
    const lf = new Float64Array(288);
    const df = new Float64Array(32);
    let idx = 0;
    for (let c = 0; c < nCk; c++) {
      ckLit.push(Float64Array.from(lf));
      ckDist.push(Float64Array.from(df));
      const upto = Math.min(S, (c + 1) * CK);
      for (; idx < upto; idx++) {
        const s = syms[idx];
        if (s.len === 1) lf[data[s.pos]]++;
        else {
          lf[LEN_CODE_OF_LEN[s.len]]++;
          df[DIST_CODE_OF_DIST[s.dist]]++;
        }
      }
    }
  }
  function rangeCounts(s0, s1) {
    const lf = new Float64Array(288);
    const df = new Float64Array(32);
    const c0 = Math.floor(s0 / CK);
    const c1 = Math.floor(s1 / CK);
    for (let i = 0; i < 288; i++) lf[i] = ckLit[c1][i] - ckLit[c0][i];
    for (let i = 0; i < 32; i++) df[i] = ckDist[c1][i] - ckDist[c0][i];
    for (let i = c1 * CK; i < s1; i++) {
      const s = syms[i];
      if (s.len === 1) lf[data[s.pos]]++;
      else {
        lf[LEN_CODE_OF_LEN[s.len]]++;
        df[DIST_CODE_OF_DIST[s.dist]]++;
      }
    }
    for (let i = c0 * CK; i < s0; i++) {
      const s = syms[i];
      if (s.len === 1) lf[data[s.pos]]--;
      else {
        lf[LEN_CODE_OF_LEN[s.len]]--;
        df[DIST_CODE_OF_DIST[s.dist]]--;
      }
    }
    lf[256]++;
    return { litFreq: lf, distFreq: df };
  }
  const rangeCostCache = new Map();
  function rangeCost(s0, s1) {
    const key = s0 * 1048576 + s1;
    let v = rangeCostCache.get(key);
    if (v === undefined) {
      const c = rangeCounts(s0, s1);
      v = blockCostEstimate(c.litFreq, c.distFreq);
      rangeCostCache.set(key, v);
    }
    return v;
  }
  function trySplit(s0, s1, depth) {
    if (s1 - s0 < 8192 || depth > 6) return [s0, s1];
    const whole = rangeCost(s0, s1);
    let bestGain = 0;
    let bestAt = -1;
    for (const frac of [0.25, 0.5, 0.75]) {
      const at = s0 + Math.floor(((s1 - s0) * frac) / CK) * CK;
      if (at <= s0 || at >= s1) continue;
      const gain = whole - rangeCost(s0, at) - rangeCost(at, s1);
      if (gain > bestGain) {
        bestGain = gain;
        bestAt = at;
      }
    }
    if (bestAt < 0) return [s0, s1];
    const left = trySplit(s0, bestAt, depth + 1);
    const right = trySplit(bestAt, s1, depth + 1);
    return left.slice(0, -1).concat(right);
  }
  const boundaries = trySplit(0, S, 0);
  let best = emitZlibStream(data, syms, [0, S]);
  if (boundaries.length > 2) {
    const split = emitZlibStream(data, syms, boundaries);
    if (split.length < best.length) best = split;
    if (allowReparse) {
      const syms2 = [];
      const bnds2 = [0];
      for (let b = 0; b < boundaries.length - 1; b++) {
        const s0 = boundaries[b];
        const s1 = boundaries[b + 1];
        const byteStart = syms[s0].pos;
        const byteEnd = s1 < S ? syms[s1].pos : N;
        const c = rangeCounts(s0, s1);
        const bc = costsFromLengths(huffmanLengths(c.litFreq, 15), huffmanLengths(c.distFreq, 15));
        dpParse(data, matches, bc.litCost, bc.lenCost, bc.distCost, byteStart, byteEnd, dp, backPrev, backLen, backDist, 12);
        const bs = collectSymbols(backPrev, backLen, backDist, byteStart, byteEnd);
        for (const s of bs) syms2.push(s);
        bnds2.push(syms2.length);
      }
      const reparsed = emitZlibStream(data, syms2, bnds2);
      if (reparsed.length < best.length) best = reparsed;
    }
  }
  return { stream: best, symCount: S };
}

function optimalDeflate(data, dualInit) {
  const N = data.length;
  const matches = findMatches(data);
  const work = {
    dp: new Float64Array(N + 1),
    backPrev: new Int32Array(N + 1),
    backLen: new Uint16Array(N + 1),
    backDist: new Uint32Array(N + 1),
  };
  const allowReparse = true;
  // Frequency-seeded initial costs.
  const bf = new Float64Array(256).fill(1);
  for (let i = 0; i < N; i++) bf[data[i]]++;
  const freqLitCost = new Float64Array(288);
  for (let i = 0; i < 256; i++) freqLitCost[i] = -Math.log2(bf[i] / (N + 256));
  for (let i = 256; i < 288; i++) freqLitCost[i] = 8;
  const freqLenCost = new Float64Array(259);
  for (let len = 3; len <= 258; len++) freqLenCost[len] = 8 + LEN_EXTRA_BITS[len];
  const freqDistCost = new Float64Array(32769);
  for (let d = 1; d <= 32768; d++) freqDistCost[d] = 5 + DIST_EXTRA_BITS[d];
  const first = optimalParsePath(data, matches, work, { litCost: freqLitCost, lenCost: freqLenCost, distCost: freqDistCost }, allowReparse);
  let best = first.stream;
  // Grey streams can converge to a better parse from fixed-Huffman
  // seeded costs, but only when the frequency-seeded parse stays
  // literal-heavy (many symbols per byte); when it already parses
  // into long matches, the second path cannot beat it.
  if (dualInit && first.symCount > N / 16) {
    const fixedLitLens = new Uint8Array(288);
    for (let i = 0; i < 288; i++) fixedLitLens[i] = i < 144 ? 8 : i < 256 ? 9 : i < 280 ? 7 : 8;
    const fixedDistLens = new Uint8Array(32).fill(5);
    const alt = optimalParsePath(data, matches, work, costsFromLengths(fixedLitLens, fixedDistLens), allowReparse);
    if (alt.stream.length < best.length) best = alt.stream;
  }
  return best;
}

// ---------------------------------------------------------------------------
// Image encoding: zlib trials over all candidates, then optimal DEFLATE
// on the winning stream.
// ---------------------------------------------------------------------------
function encodeImage(image) {
  const info = analyseImage(image.pixels);
  const candidates = buildCandidates(image, info);
  let best = null;
  let bestCandidate = null;
  let bestNonPaletteLength = Infinity;

  const ordered = candidates.filter((c) => !c.palette).concat(candidates.filter((c) => c.palette));
  for (const candidate of ordered) {
    const prep = computeRowCostsAndCache(candidate.raw, image.width, image.height, candidate.bpp);
    const defs = streamDefsFor(image, candidate, prep);
    let result;
    if (candidate.palette && bestNonPaletteLength !== Infinity) {
      // Screen: a palette candidate whose unfiltered stream already loses
      // to the best non-palette PNG by more than 3% cannot win through
      // filtered streams (palette wins come from index entropy, which
      // the unfiltered stream already captures), so skip its other trials.
      const fixed0 = defs.filter((d) => d.filters.every((f) => f === 0));
      result = evaluateDefs(image, candidate, prep, fixed0);
      if (result.png.length > bestNonPaletteLength * 1.03) {
        // Keep the fixed0 result in the pool; it cannot be the winner
        // unless every non-palette result is somehow larger, which the
        // screen condition excludes.
        if (best === null || result.png.length < best.png.length) {
          best = result;
          bestCandidate = candidate;
        }
        continue;
      }
      const rest = defs.filter((d) => !d.filters.every((f) => f === 0));
      const restResult = evaluateDefs(image, candidate, prep, rest);
      if (restResult.png.length < result.png.length) result = restResult;
    } else {
      result = evaluateDefs(image, candidate, prep, defs);
    }
    if (!candidate.palette && result.png.length < bestNonPaletteLength) {
      bestNonPaletteLength = result.png.length;
    }
    if (best === null || result.png.length < best.png.length) {
      best = result;
      bestCandidate = candidate;
    }
  }

  const dualInit = bestCandidate.colorType === 0 || bestCandidate.colorType === 4;
  const optimal = optimalDeflate(best.stream, dualInit);
  const inflated = zlib.inflateSync(optimal);
  if (inflated.equals(Buffer.from(best.stream))) {
    const png = assemblePng(image.width, image.height, bestCandidate, optimal);
    if (png.length < best.png.length) return png;
  }
  return best.png;
}

// ---------------------------------------------------------------------------
// Entry point: process the eight fixed instances.
// ---------------------------------------------------------------------------
for (let n = 1; n <= IMAGE_COUNT; n++) {
  const id = 'i' + String(n).padStart(3, '0');
  const input = fs.readFileSync(path.join(INPUT_DIR, id, 'image.png'));
  const image = decodePng(input);
  const output = encodeImage(image);
  const outputDir = path.join(OUTPUT_DIR, id);
  fs.mkdirSync(outputDir, { recursive: true });
  fs.writeFileSync(path.join(outputDir, 'image.png'), output);
}
