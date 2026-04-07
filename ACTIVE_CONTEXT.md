Active Context for Fiat Crypto
Do not change the format of this file. This file should be continuously updated but stay relatively concise and readable. Old issues and completed items should be completely removed.
This file is for both me an agents, so clarify who should be working on something if its ambiguous. E.g. proofs are always for me unless otherwise stated.


# Current Focus
The high level of what we are currently working on.

- Extending equivalence checker to handle more AVX primitives beyond add/sub.
- Building out a test suite of AVX assembly programs to drive incremental instruction/rewrite rule support.
- Determining the placement of the Batching Transformation in the synthesis pipeline.


# Recent Updates
What we've thought about or accomplished recently, as far as it's relevant to moving forward.

- **Vectorize.v synthesis PoC PASSES**: `src/Assembly/Vectorize.v` synthesizes AVX2 assembly from scalar op specs. `vectorized_add "fiat_25519_add" 5` generates 5× vpaddq on YMM regs. The generated assembly passes the equivalence checker (`n=20` trick). This is the first step toward automated scalar→vector assembly synthesis in Coq.
- **Batched add PoC PASSES**: `test-asm/batch_avx_add.asm` — hand-written version also passes. Both hand-written and synthesized produce identical logic.
- **Batched carry_mul pipeline**: `batched_carry_mulmod` in `SIMDUnsaturatedSolinas.v` applies `carry_mulmod` to 4 independent slices. Reification succeeded (~7s). Pipeline def + registration added to `UnsaturatedSolinas.v`.
- Set up unified test suite: `test-asm/run-tests.sh` + `test-asm/test-manifest.tsv`. 5 tests (add/sub × xmm/ymm + batch add).
- Added `vpbroadcastq` and `vpblendd` (all three files: Syntax, Semantics, Symbolic). These were needed for ymm sub.
- Re-added `sub_to_add_neg` rewrite rule (was removed in `1843b077`, which broke xmm sub equivalence).
- Proved all rewrite rule lemmas in Symbolic.v
------------------------------------------------------


# Active Issues & Blockers
These are the bugs/specific issues that we need to resolve to move forward.

- **SymbolicProofs.v `GetOperand_R`**: Needs updating for 128/256-bit Load cases.

------------------------------------------------------


# Next Steps
What to do immediately, in order of priority.

- Extend Vectorize.v: test `vectorized_sub` through the equivalence checker (needs underflow constants from the spec)
- Generalize Vectorize.v: support more ops, eventually handle carry_mul decomposition (mulhuu → vpmuludq combinations)
- Once binary builds: generate batched carry_mul C code, verify it's 4× the scalar version
- Write scalar assembly for batched carry_mul (4 independent carry_muls), test equivalence check
- Generalize the batching pattern: make `batched_X` work for any operation, not just carry_mul
