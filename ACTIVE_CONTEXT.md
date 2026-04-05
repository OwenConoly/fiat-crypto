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

- **Batched add PoC PASSES**: `test-asm/batch_avx_add.asm` — 5× `vpaddq` on YMM regs does 20 element-wise adds (4× field add). Equivalence check passes by using `n=20` with the existing `add` pipeline. Test added to manifest, all 5 tests pass.
- **Batched carry_mul pipeline**: Building `batch_carry_mul` operation. Defined `batched_carry_mulmod` in `SIMDUnsaturatedSolinas.v` (applies `carry_mulmod` to 4 independent slices of flat input lists). Reification succeeded (~7s). Pipeline def + registration added to `UnsaturatedSolinas.v`. Binary rebuild in progress.
- Set up unified test suite: `test-asm/run-tests.sh` + `test-asm/test-manifest.tsv`. 5 tests (add/sub × xmm/ymm + batch add).
- Added `vpbroadcastq` and `vpblendd` (all three files: Syntax, Semantics, Symbolic). These were needed for ymm sub.
- Re-added `sub_to_add_neg` rewrite rule (was removed in `1843b077`, which broke xmm sub equivalence). Proof is Admitted.

------------------------------------------------------


# Active Issues & Blockers
These are the bugs/specific issues that we need to resolve to move forward.

- **`sub_to_add_neg_ok` proof** (me): Admitted in Symbolic.v ~line 2526. Normalizes `sub s [a; b]` to `add s [a; neg s [b]]`.
- **`peel_disjoint_set_slices_eval` proof** (me): Admitted in Symbolic.v ~line 2568. Base case `cbn` doesn't simplify — asked Slack.
- **`slice_set_slice_disjoint_ok` proof** (me): Admitted in Symbolic.v ~line 2580. Depends on `peel_disjoint_set_slices_eval`.
- **SymbolicProofs.v `GetOperand_R`**: Needs updating for 128/256-bit Load cases.

------------------------------------------------------


# Next Steps
What to do immediately, in order of priority.

- Fix the three Admitted proofs above (me)
- Once binary builds: generate batched carry_mul C code, verify it's 4× the scalar version
- Write scalar assembly for batched carry_mul (4 independent carry_muls), test equivalence check
- Eventually write AVX assembly for carry_mul (hard — cross-limb products, carries)
- Generalize the batching pattern: make `batched_X` work for any operation, not just carry_mul
- Batching Transformation: define scalar→vector DAG mapping, decide pipeline placement
