# Notes

Majority written by Claude Code. 
Technical discoveries, debugging notes, and patterns that took effort to figure out. 
Try to keep this file to information that will be continually relevant, learned patterns about the codebase, etc. NOT just things that are true right now (like a the state of built binaries).

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