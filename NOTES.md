# Notes

Majority written by Claude Code. 
Technical discoveries, debugging notes, and patterns that took effort to figure out. 
Try to keep this file to information that will be continually relevant, learned patterns about the codebase, etc. NOT just things that are true right now (like a the state of built binaries).

## peel_disjoint_set_slices won't reduce in proofs (2026-04-01)

`cbn [peel_disjoint_set_slices]`, `simpl`, `cbv`, and `unfold` all fail to reduce `peel_disjoint_set_slices lo1 s1 inner 0` to `ExprApp (slice lo1 s1, [inner])` in the base case of the induction proof, even though fuel is literally `0`. The `%N` scope on the Fixpoint or some opacity issue may be blocking reduction. `change ... with ...` was suggested but untested. Worth asking on Slack/Zulip — this is a Coq reduction behavior issue, not a math issue.


## YMM set_slice chain depth problem (2026-03-29)

When `vector_binop_idx` builds a 4-lane (YMM) result, it creates a chain:
```
set_slice 192 64 (set_slice 128 64 (set_slice 64 64 (add_lane0, add_lane1), add_lane2), add_lane3)
```

When `Store` later extracts lanes via `slice 0 64`, `slice 64 64`, etc., each `App` call runs rewrites once. With XMM (2 lanes, 1-deep chain), one pass of `slice_set_slice_disjoint` suffices. With YMM (4 lanes, 3-deep chain), `slice 0 64` needs to peel through 3 disjoint `set_slice` layers.

We added a recursive `peel_disjoint_set_slices` to handle the disjoint case (fuel=8). This fixed limb 0 extraction but limb 1 (`slice 64 64`) still fails — the non-disjoint `slice_set_slice` rule doesn't fire for unknown reasons. The recursive approach may not be the right solution; the root cause could be deeper (reveal depth, rewrite ordering, or how the Store interacts with the vector result construction).

Key DAG nodes from the failing run:
- 667 = `set_slice 64 64 [12, 666]` (base=limb0_add, val=limb1_add)
- 675 = `slice 64 64 [667]` (should simplify to `slice 0 64 [666]` via slice_set_slice, but doesn't)


## Proving peel_disjoint_set_slices correct (2026-03-31)

The `peel_disjoint_set_slices` function recursively strips disjoint `set_slice` layers from an expression before slicing. To prove `slice_set_slice_disjoint_ok`, you need a helper lemma:

```coq
Lemma peel_disjoint_set_slices_eval G d lo1 s1 inner v fuel :
  gensym_dag_ok G d ->
  eval G d (ExprApp (slice lo1 s1, [inner])) v ->
  eval G d (peel_disjoint_set_slices lo1 s1 inner fuel) v.
```

**Proof:** Induction on `fuel`.
- Base (O): returns `ExprApp (slice lo1 s1, [inner])` — exact hypothesis.
- Step (S fuel'): case split on `inner`:
  - Not `set_slice` or disjointness check fails → returns the slice expr → exact hypothesis.
  - `ExprApp (set_slice lo2 s2, [base; val])` with disjointness true:
    1. Invert `eval` on hypothesis to get `eval G d base v_base` and `eval G d val v_val`.
    2. Construct `eval G d (ExprApp (slice lo1 s1, [base])) (slice_result_of v_base)` using `EApp`.
    3. Show the Z values are equal: `slice lo1 s1 (set_slice lo2 s2 a b) = slice lo1 s1 a` when disjoint. This is a `Z.bitblast` fact.
    4. Apply IH.

The Z disjointness fact: if `lo1 + s1 <= lo2` or `lo2 + s2 <= lo1`, then:
`Z.land (Z.shiftr (Z.lor (Z.shiftl (Z.land b (Z.ones s2)) lo2) (Z.ldiff a (Z.shiftl (Z.ones s2) lo2))) lo1) (Z.ones s1) = Z.land (Z.shiftr a lo1) (Z.ones s1)`

Key `eval` facts used:
- `eval` has two constructors: `ERef` (DAG lookup) and `EApp` (direct application via `interp_op`)
- `interp_op` for `slice lo sz [a]` = `Z.land (Z.shiftr a lo) (Z.ones sz)`
- `interp_op` for `set_slice lo sz [a; b]` = `Z.lor (Z.shiftl (Z.land b (Z.ones sz)) lo) (Z.ldiff a (Z.shiftl (Z.ones sz) lo))`
- `eval_eval` gives determinism: `eval G d e v1 -> eval G d e v2 -> v1 = v2`
- The `t` tactic does initial inversion/unfolding; the helper lemma is applied after `t`.


## Load/Store decomposition (no DAG ops needed)

256-bit Load decomposes into 4x Load64 + set_slice chain (Symbolic.v:4472-4487).
256-bit Store decomposes into 4x slice + Store64 (Symbolic.v:4537-4551).
vmovdqu doesn't need a DAG-level op — it's fully handled by Load/Store decomposition.
Same pattern as 128-bit (2x Load64/Store64).


## vmovdqu/vpaddq/vzeroupper already have full YMM symex

All three were already implemented before we tried simple_avx_add_ymm.asm:
- vmovdqu: generic move, size inferred from operand (Symbolic.v:4677)
- vpaddq: SymexVectorOp auto-scales lanes (s/64), YMM = 4 lanes (Symbolic.v:4686)
- vzeroupper: loops all 16 YMM regs, slices lower 128 (Symbolic.v:4894)


## combine_consts / simp_inside

When debugging rewrite rules that "should fire but don't", check whether the
expression was created inside `combine_consts` rather than via normal `App` calls.
`combine_consts` has its own internal simplification pipeline (`simp_inside`) that
is separate from the main rewrite pass chain. If a new rewrite rule is needed inside
that pipeline, it must be added to `simp_inside` explicitly (around line 3650 in Symbolic.v).
The main rewrite passes only fire via `App` -> `simplify`, not via `merge`.