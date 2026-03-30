# test-asm/

Test assembly files for the AVX equivalence checker. Each file implements curve25519 field addition (or subtraction) using different instruction strategies, progressing from scalar baseline to full batched AVX2.


## Equivalence check test files

All of these implement `fiat_25519_add` or `fiat_25519_sub` and can be checked with `unsaturated_solinas --hints-file`.

| File | Status | What it tests |
|------|--------|---------------|
| `simple_scalar_add.asm` | PASSES | Baseline scalar add. 5 individual `mov`/`add`/`mov` sequences. |
| `simple_avx_add.asm` | PASSES | XMM vectorized add. `vpaddq` on pairs of limbs, `vmovq` for the 5th. |
| `simple_avx_sub.asm` | PASSES | XMM vectorized sub. Tests `vpsubq` and `sub_to_add_neg` rewrite rule. |
| `simple_avx_add_lane1.asm` | BLOCKED | Lane 1 variant (upper 64 bits of XMM). Needs symex for: `vpxor`, `vpunpcklqdq`, `vpextrq`. |
| `simple_avx_add_lane2.asm` | BLOCKED | Lane 2 variant (bits 128-191 of YMM). Needs symex for: `vperm2i128`, `vextracti128`, `vzeroupper`. |
| `simple_avx_add_lane3.asm` | BLOCKED | Lane 3 variant (bits 192-255 of YMM). Needs all of the above. |
| `wrapped_avx_add.asm` | FUTURE | Full batched AVX2 add with gather/scatter. Needs many more opcodes (`vpgatherdq`, `vpinsrd`, etc.). |


## Scripts

| File | Purpose |
|------|---------|
| `check-simple-add.sh` | Runs equivalence check on `simple_avx_add.asm`, prints PASS/FAIL. |
| `test_add.sh` | Syncs files to remote Linux server, assembles with NASM, links against `test_add.c`, runs. Needed because dev machine is ARM Mac. |
| `test_add.c` | C test harness. Links against any `fiat_25519_add` implementation and checks 1000 random inputs against `a[i] + b[i]`. |


## Running equivalence checks

```sh
# From repo root:
src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
  25519 64 '(auto)' '2^255 - 19' add \
  --hints-file test-asm/simple_avx_add.asm -o /dev/null --output-asm /dev/null

# For sub:
src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
  25519 64 '(auto)' '2^255 - 19' sub \
  --hints-file test-asm/simple_avx_sub.asm -o /dev/null --output-asm /dev/null
```
