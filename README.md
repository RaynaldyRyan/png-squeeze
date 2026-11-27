# png-squeeze

Lossless PNG re-encoder that squeezes 1280x720 RGBA screenshots into the smallest valid PNG it can find.

[![make.fun](https://make.fun/badge/png-squeeze-01-run-20261127.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)
[![rank](https://make.fun/badge/png-squeeze-01-run-20261127/RaynaldyRyan/png-squeeze/rank.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)
[![reward](https://make.fun/badge/png-squeeze-01-run-20261127/RaynaldyRyan/png-squeeze/reward.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)

## Run

Place the eight input images at `/input/i001/image.png` through `/input/i008/image.png`, then run:

```sh
node main.ts
```

Each re-encoded image is written to `/output/<id>/image.png`. For local testing, set `MAKEFUN_INPUT_DIR` and `MAKEFUN_OUTPUT_DIR` (or `INPUT_DIR` and `OUTPUT_DIR`) to override the input and output roots.
