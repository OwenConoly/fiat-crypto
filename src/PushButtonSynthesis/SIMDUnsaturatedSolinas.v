(** * Push-Button Synthesis of SIMD-Vectorized Unsaturated Solinas *)
(** Wraps [UnsaturatedSolinas] operations with [batch_expr] to produce
    expressions suitable for AVX2 (n=4 lanes) or AVX-512 (n=8 lanes).
    The batched expression is passed through the standard
    [Pipeline.BoundsPipeline]; [PartialEvaluate] inside will unroll the
    [List_map] nodes once the batch-sized bounds are provided. *)
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import String.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Language.API.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.SIMDBatch.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinasReificationCache.
Require Import Crypto.PushButtonSynthesis.Primitives.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Import ListNotations.

Import API.Compilers.
Import Language.Compilers.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Set Keyed Unification.

Local Opaque
      reified_carry_mul_gen
      reified_carry_square_gen
      reified_carry_scmul_gen
      reified_carry_gen
      reified_add_gen
      reified_sub_gen
      reified_opp_gen
      reified_carry_add_gen
      reified_carry_sub_gen
      reified_carry_opp_gen
      expr.Interp.

Section __.
  Context {output_language_api : ToString.OutputLanguageAPI}
          {pipeline_opts : PipelineOptions}
          {pipeline_to_string_opts : PipelineToStringOptions}
          {synthesis_opts : SynthesisOptions}
          {tight_upperbound_fraction : tight_upperbound_fraction_opt}
          (n : nat)
          (s : Z)
          (c : list (Z * Z))
          (machine_wordsize : machine_wordsize_opt)
          (simd_lanes : nat).  (* 4 for AVX2, 8 for AVX-512 *)

  Local Notation limbwidth := (limbwidth n s c).
  Local Notation tight_bounds := (tight_bounds n s c) (only parsing).
  Local Notation loose_bounds := (loose_bounds n s c) (only parsing).

  (** Batch bounds: repeat the per-element bounds [simd_lanes] times. *)
  Local Notation batch_loose_bounds :=
    (Some (List.repeat (Some loose_bounds) simd_lanes)) (only parsing).
  Local Notation batch_tight_bounds :=
    (Some (List.repeat (Some tight_bounds) simd_lanes)) (only parsing).

  (** TODO: add batched pipeline definitions here, e.g.:

  Definition batch_carry_mul :=
    Pipeline.BoundsPipeline
      false (* subst01 *)
      possible_values
      (batch_expr
        (reified_carry_mul_gen
          @ GallinaReify.Reify (Qnum limbwidth)
          @ GallinaReify.Reify (Z.pos (Qden limbwidth))
          @ GallinaReify.Reify s
          @ GallinaReify.Reify c
          @ GallinaReify.Reify n
          @ GallinaReify.Reify idxs)
        simd_lanes)
      (batch_loose_bounds, (batch_loose_bounds, tt))
      batch_tight_bounds.
  *)

End __.
