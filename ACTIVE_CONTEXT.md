Active Context for Fiat Crypto
Do not change the format of this file. This file should be continuously updated but stay relatively concise and readable. Old issues and completed items should be completely removed. 
This file is for both me an agents, so clarify who should be working on something if its ambiguous. E.g. proofs are always for me unless otherwise stated.


# Current Focus
The high level of what we are currently working on.

- Extending equivalence checker to handle more AVX primitives beyond add/sub.
- Determining the placement of the Batching Transformation in the synthesis pipeline.

------------------------------------------------------


# Active Issues & Blockers
These are the bugs/specific issues that we need to resolve to move forward.

- sub_to_add_neg proof is Admitted
  The rewrite rule works correctly but the Coq proof is admitted.
  Goal after `t.`: show (y + (-y0 mod 2^s)) mod 2^s = (y - y0) mod 2^s.
  Should be straightforward with Zplus_mod_idemp_r but needs massage to match goal shape.

- Symbolic Proofs: GetOperand_R in SymbolicProofs.v needs updating for 128/256-bit Load cases.

------------------------------------------------------


# Next Steps
What to do immediately, in order of priority.

- Clean up test-asm directory. No random old files, everything should have a use. clarify the workflow and meaning of each file in a dir-specific claude.md.

- Complex Primitives: Try carry_mul or other operations through the equivalence checker.

- Batching Transformation: Recover the "forgotten" solution from the last meeting.
	Define the mapping: Scalar DAG Ops -> Vector DAG Ops.
	Decide on pipeline placement (Pre-synthesis vs. Mid-synthesis?).



Key Insight: combine_consts / simp_inside
------------------------
When debugging rewrite rules that "should fire but don't", check whether the
expression was created inside `combine_consts` rather than via normal `App` calls.
`combine_consts` has its own internal simplification pipeline (`simp_inside`) that
is separate from the main rewrite pass chain. If a new rewrite rule is needed inside
that pipeline, it must be added to `simp_inside` explicitly (around line 3650 in Symbolic.v).
The main rewrite passes only fire via `App` -> `simplify`, not via `merge`.
