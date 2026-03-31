Active Context for Fiat Crypto
Do not change the format of this file. This file should be continuously updated but stay relatively concise and readable. Old issues and completed items should be completely removed. 
This file is for both me an agents, so clarify who should be working on something if its ambiguous. E.g. proofs are always for me unless otherwise stated.


# Current Focus
The high level of what we are currently working on.

- Extending equivalence checker to handle more AVX primitives beyond add/sub.
- Determining the placement of the Batching Transformation in the synthesis pipeline.


# Recent Updates
What we've thought about or accomplished recently, as far as it's relevent to moving forward.

- Eliminated `sub_to_add_neg` rewrite rule entirely. Changed `slice_vsub` to emit `add(x, neg(y))` directly instead of `sub(x, y)`, matching what PHOAS produces. This removes an admitted proof and one rewrite pass. The `slice_vsub_ok` proof needs updating — the new goal is `(a + (-b mod 2^s)) mod 2^s = (a - b) mod 2^s` which is provable (outer mod washes out inner mod, unlike the old stuck goal).
- Decided against premature generalization of slice_vadd/slice_vsub — will add 1-2 more concrete vector ops first (vxor, vand) then generalize once the pattern is clear.

------------------------------------------------------


# Active Issues & Blockers
These are the bugs/specific issues that we need to resolve to move forward.

- slice_vsub_ok proof needs updating (for me) — new goal is `(a + (-b mod 2^s)) mod 2^s = (a - b) mod 2^s`, should be straightforward with Zplus_mod_idemp_r.

- slice_set_slice_disjoint proof is Admitted (after making it recursive with peel_disjoint_set_slices).

- Symbolic Proofs: GetOperand_R in SymbolicProofs.v needs updating for 128/256-bit Load cases.

------------------------------------------------------


# Next Steps
What to do immediately, in order of priority.


- Add more vector ops (vxor, vand) as concrete DAG ops with slice rules, then generalize.

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
