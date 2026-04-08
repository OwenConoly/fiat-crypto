Active Context for Fiat Crypto
Do not change the format of this file. This file should be continuously updated but stay relatively concise and readable. Old issues and completed items should be completely removed.
This file is for both me an agents, so clarify who should be working on something if its ambiguous. E.g. proofs are always for me unless otherwise stated.


# Current Focus
The high level of what we are currently working on.

- Carry_mul equivalence checking now works (scalar and batched). Next: vectorized carry_mul using AVX2 instructions.
- Building out a test suite of AVX assembly programs to drive incremental instruction/rewrite rule support.
- Adding symex for vector instructions needed by a true AVX2 carry_mul (vpmuludq, vpsrlq, vpsllq, etc.).


# Recent Updates
What we've thought about or accomplished recently, as far as it's relevant to moving forward. Mention specific files edited.

- **Batched carry_mul equivalence check PASSES**: `test-asm/batch_avx_carry_mul.asm` inlines 4 sequential copies of the scalar carry_mul body (from `fiat-amd64/`) with AoS memory offsets (+0x28 per element). Requires `--no-wide-int --shiftr-avoid-uint1 --tight-bounds-mul-by 1.000001` flags (same as the Makefile.test-amd64-files.mk tests). Scalar carry_mul also passes with these flags.
- **Scalar carry_mul was broken** by an old SetReg change; now fixed. The `slice0` rewrite rule (`slice 0 s (mulZ ...) → mul s ...`) is essential for matching PHOAS mulZ with assembly's mulx output.
- **8 tests pass**: add/sub × xmm/ymm + batch_add + batch_sub + scalar_carry_mul + batch_carry_mul.
- Files edited: `test-asm/batch_avx_carry_mul.asm` (new), `test-asm/test-manifest.tsv` (added 2 entries).
------------------------------------------------------


# Active Issues & Blockers
These are the bugs/specific issues that we need to resolve to move forward.

- **SymbolicProofs.v `GetOperand_R`**: Needs updating for 128/256-bit Load cases.

------------------------------------------------------


# Next Steps
What to do immediately, in order of priority.

- Write a true AVX2 vectorized carry_mul (using vpmuludq, vpsrlq, vpsllq etc. instead of scalar mulx). This requires:
  1. Adding symex for vpmuludq, vpsrlq, vpsllq to Symbolic.v (+ Syntax.v, Semantics.v)
  2. Writing the vectorized assembly
  3. Possibly new rewrite rules if the DAG structures don't match
- Generalize the batching pattern: make `batched_X` easy to add for any operation
- The current batch_avx_carry_mul.asm is 4 sequential scalar copies — not actually vectorized. It proves the spec works; next step is real SIMD.
