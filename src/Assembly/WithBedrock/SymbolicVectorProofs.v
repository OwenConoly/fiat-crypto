From Coq Require Import List.
From Coq Require Import Lia.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.
From Coq Require Import NArith.
From Coq Require Import ZArith.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.Util.ErrorT.
Require	Import Crypto.Util.Option.
Import Coq.Lists.List.
Require Import Crypto.Util.ListUtil.IndexOf.
Require Import Crypto.Util.Tactics.WarnIfGoalsRemain.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.Option.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.WithBedrock.Semantics.
Require Import Crypto.Assembly.Equivalence.
Import Sorting.Permutation.

Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Memory. Import coqutil.Map.Memory.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndianList.
Import Word.Naive.

Require Import Crypto.Util.Prod.
From Crypto.Util.Tactics Require Import BreakMatch DestructHead UniquePose.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.ZUtil.Ones.
Import coqutil.Tactics.autoforward coqutil.Decidable coqutil.Tactics.Tactics.

Require Import Crypto.Assembly.WithBedrock.SymbolicProofsCore.
Import ListNotations.

Local Coercion ExprRef : idx >-> expr.

Section WithFrame.
Context (frame : mem_state -> Prop).
Section WithVectorProofs.
Context (G : symbol -> option Z).
Local Notation eval := (Symbolic.eval G).
Local Notation interp_op := (Symbolic.interp_op G).
Local Notation interprets_as_unaryop := (Symbolic.interprets_as_unaryop G).
Local Notation interprets_as_binop := (Symbolic.interprets_as_binop G).
Local Notation gensym_dag_ok := (Symbolic.gensym_dag_ok G).
Local Notation R := (R frame G).

Notation subsumed d1 d2 := (forall i v, eval d1 i v -> eval d2 i v).
Local Infix ":<" := subsumed (at level 70, no associativity).

  (* RevealConst succeeds iff the idx evaluates to a concrete constant.
     State is unchanged, and the returned Z is the value. *)
  Lemma RevealConst_R {opts : symbolic_options_computed_opt} {descr : description}
    s m (HR : R s m)
    (i : idx) (v : Z) (Hv : eval s i v)
    z s'
    (H : Symbolic.RevealConst i s = Success (z, s'))
    : s' = s /\ v = z.
  Proof using Type. Admitted.
  (*   cbv [Symbolic.RevealConst Symbolic.Reveal Symbolic.bind Symbolic.ret Symbolic.err] in H. *)
  (*   destruct (Symbolic.reveal s 1 i) eqn:Hrev; try (inversion H; fail). *)
  (*   destruct n as [[] []]; inversion_ErrorT; Prod.inversion_prod; subst. *)
  (*   split; [reflexivity|]. *)
  (*   eapply Symbolic.eval_reveal in Hrev; [|exact Hv]. *)
  (*   inversion Hrev; subst. clear Hrev. *)
  (*   inversion H2; subst. *)
  (*   cbn [Symbolic.interp_op] in H1. inversion H1. reflexivity. *)
  (* Qed. *)

  (* Extracts lane [lane_idx] of width [lane_width] from [v]. *)
  Lemma extract_lane_R {opts : symbolic_options_computed_opt} {descr : description}
    s m (HR : R s m)
    (i : idx) (v : Z) (Hv : eval s i v)
    (lane_idx : nat) (lane_width : N) (Hlw : (lane_width > 0)%N)
    res s'
    (H : SymbolicVector.extract_lane i lane_idx lane_width s = Success (res, s'))
    : R s' m /\ s :< s' /\
      eval s' res (SemanticVector.extract_lane v lane_idx (Z.of_N lane_width)).
  Proof using Type.
    unfold SymbolicVector.extract_lane, SemanticVector.extract_lane in *. 
    eapply (App_R s m) in H as (HR' & Hsubs & Heval_res).
    2: { exact HR. }
    2: { repeat (econstructor; eauto). }
    split; [exact HR' | split; [solve_subsumed| ]].
    replace (Z.of_N (N.of_nat lane_idx * lane_width)) with (Z.of_nat lane_idx * Z.of_N lane_width) in Heval_res by lia.
    exact Heval_res.
  Qed.

  (* Computes one lane of a binop: lane_op(lane i of v1, lane i of v2). *)
  Lemma make_lane_R {opts : symbolic_options_computed_opt} {descr : description}
    s m (HR : R s m)
    (i1 i2 : idx) (v1 v2 : Z)
    (Hv1 : eval s i1 v1) (Hv2 : eval s i2 v2)
    (lane_op : op) (binop : Z -> Z -> Z)
    (Hop : interprets_as_binop lane_op binop)
    (lane_idx : nat) (lane_width : N) (Hlw : (lane_width > 0)%N)
    res s'
    (H : SymbolicVector.make_lane i1 i2 lane_op lane_idx lane_width s
        = Success (res, s'))
    : R s' m /\ s :< s' /\
      eval s' res (SemanticVector.make_lane v1 v2 binop lane_idx (Z.of_N lane_width)).
  Proof using Type. 
    unfold SymbolicVector.make_lane, SemanticVector.make_lane in *. repeat step_symex; cbv [fst snd] in *. 
    eapply extract_lane_R in HSl1 as (HR1 & Hsubs1 & Heval_lane1); try eassumption.
    eapply extract_lane_R in HSl2 as (HR2 & Hsubs2 & Heval_lane2); try eassumption.
    eapply (App_R s1 m) in H as (HR' & Hsubs' & Heval_res); [| exact HR2 |].
    2: { 
      econstructor.
      - constructor; [eapply Hsubs2; exact Heval_lane1
                    | constructor; [exact Heval_lane2 | constructor]].
      - cbn [interp_op]. apply Hop.
    }
    split; [exact HR' | split; [solve_subsumed| ]].
    exact Heval_res. eauto. 
  Qed.

  Lemma insert_lane_ldiff_lor acc_val lane_val lane_width lane_idx :
    lane_width > 0 ->
    Z.shiftr acc_val (Z.of_nat lane_idx * lane_width) = 0 ->
    Z.lor
      (SemanticVector.insert_lane lane_val lane_idx lane_width)
      (Z.ldiff acc_val
        (Z.shiftl (Z.ones lane_width)
        (Z.of_nat lane_idx * lane_width)))
    = Z.lor acc_val (SemanticVector.insert_lane lane_val lane_idx lane_width).
  Proof. intros. 
    rewrite Z.lor_comm.
    f_equal. bitblast.Z.bitblast. assert (Hbit : Z.testbit acc_val i = false).
    { replace i with ((i - (Z.of_nat lane_idx * lane_width)) + (Z.of_nat lane_idx * lane_width)) by lia.
      rewrite <- Z.shiftr_spec by lia.
      rewrite H0. apply Z.bits_0. }
    rewrite Hbit. reflexivity.
  Qed.

  (* Writes [lane_val] into lane [lane_idx] of accumulator [acc]. *)
  Lemma insert_lane_R {opts : symbolic_options_computed_opt} {descr : description}
    s m (HR : R s m)
    (acc lane : idx) (acc_val lane_val : Z)
    (Hacc : eval s acc acc_val) (Hlane : eval s lane lane_val)
    (lane_idx : nat) (lane_width : N) (Hlw : (lane_width > 0)%N)
    res s'
    (H : SymbolicVector.insert_lane acc lane lane_idx lane_width s
        = Success (res, s'))
    : R s' m /\ s :< s' /\
      eval s' res
        (Z.lor (SemanticVector.insert_lane lane_val lane_idx (Z.of_N lane_width))
              (Z.ldiff acc_val
                  (Z.shiftl (Z.ones (Z.of_N lane_width))
                            (Z.of_nat lane_idx * Z.of_N lane_width)))).
  Proof using Type. 
    cbv [SymbolicVector.insert_lane SemanticVector.insert_lane] in *. 
    eapply (App_R s m) in H as (HR' & Hsubs' & Heval_res). 
    split; [|split]; try eauto. exact HR. repeat (eauto || econstructor). cbn [interp_op]. 
    replace (Z.of_N (N.of_nat lane_idx * lane_width)) with (Z.of_nat lane_idx * Z.of_N lane_width) by lia.
    reflexivity.
  Qed.

  (* inductive case of vector_binop_aux_R *)
  Lemma vector_binop_aux_S_lane_idx
    {opts : symbolic_options_computed_opt} {descr : description}
    (i1 i2 : idx) (lane_op : op)
    (lane_idx n : nat) (lane_width : N) (acc : idx) s res s'
    (H : SymbolicVector.vector_binop_aux i1 i2 lane_op lane_idx (S n)
          lane_width acc s = Success (res, s'))
    : exists lane_val new_acc s1 s2,
        SymbolicVector.make_lane i1 i2 lane_op lane_idx lane_width s
          = Success (lane_val, s1)
    /\ SymbolicVector.insert_lane acc lane_val lane_idx lane_width s1
          = Success (new_acc, s2)
    /\ SymbolicVector.vector_binop_aux i1 i2 lane_op (S lane_idx) n lane_width
          new_acc s2 = Success (res, s').
  Proof. simpl SymbolicVector.vector_binop_aux in *. repeat step_symex; cbv [fst snd] in *. 
    exists lane_val, new_acc, s0, s1. split; [| split]; eassumption.
  Qed.

  Lemma acc_range_preserved : forall (acc_val lane_res lane_width : Z) (lane_idx : nat),
    lane_width > 0 ->
    Z.shiftr acc_val (Z.of_nat lane_idx * lane_width) = 0 ->
    let new_acc_val := Z.lor
        (Z.shiftl (Z.land lane_res (Z.ones lane_width)) (Z.of_nat lane_idx * lane_width))
        (Z.ldiff acc_val (Z.shiftl (Z.ones lane_width) (Z.of_nat lane_idx * lane_width)))
    in
    Z.shiftr new_acc_val (Z.of_nat (S lane_idx) * lane_width) = 0.
  Proof.
      intros. 
    apply Z.bits_inj_iff'; intros i Hi.
    rewrite Z.shiftr_spec by lia.
    rewrite Z.bits_0. subst new_acc_val.
    rewrite Z.lor_spec.
    (* Show both parts of the lor are 0 at position (S lane_idx) * lane_width + i *)
    rewrite Z.shiftl_spec by lia.
    rewrite Z.ldiff_spec.
    (* The inserted lane occupies [lane_idx * lw, (lane_idx+1) * lw) *)
    (* Position we're checking: (S lane_idx) * lw + i = (lane_idx + 1) * lw + i *)
    (* This is >= (lane_idx + 1) * lw, so above the inserted lane *)
    assert (Hins : Z.testbit (Z.land lane_res (Z.ones lane_width))
                  (i + Z.of_nat (S lane_idx) * lane_width - Z.of_nat lane_idx * lane_width) = false).
    { rewrite Z.land_spec, Z.testbit_ones_nonneg by lia.
      destruct (_ <? _) eqn:E. 
      apply Z.ltb_lt in E. lia. rewrite Bool.andb_false_r. reflexivity. }
    rewrite Hins. 
    (* Now show acc_val bit is 0 *)
    assert (Hacc_bit : Z.testbit acc_val (Z.of_nat (S lane_idx) * lane_width + i) = false).
    { 
    set (lo := Z.of_nat lane_idx * lane_width) in *.
    replace (Z.of_nat (S lane_idx) * lane_width + i) with (lane_width + i + lo) by (unfold lo; lia).
    rewrite <- (Z.shiftr_spec acc_val lo (lane_width + i)) by lia.
    rewrite H0, Z.bits_0. reflexivity.
    }
    rewrite Bool.orb_false_l.
    replace (i + Z.of_nat (S lane_idx) * lane_width) with (Z.of_nat (S lane_idx) * lane_width + i) by lia.
    rewrite Hacc_bit. reflexivity.
  Qed.

  (* Iterates [num_remaining] lanes starting at [lane_idx], folding each into [acc]. *)
  Lemma vector_binop_aux_R {opts : symbolic_options_computed_opt} {descr : description}
        s m (HR : R s m)
        (i1 i2 : idx) (v1 v2 : Z)
        (Hv1 : eval s i1 v1) (Hv2 : eval s i2 v2)
        (lane_op : op) (binop : Z -> Z -> Z)
        (Hop : interprets_as_binop lane_op binop)
        (lane_idx num_remaining : nat)
        (lane_width : N) (Hlw : (lane_width > 0)%N)
        (acc : idx) (acc_val : Z) (Hacc : eval s acc acc_val)
        (Hacc_hi : Z.shiftr acc_val (Z.of_nat lane_idx * Z.of_N lane_width) = 0)
        res s'
        (H : SymbolicVector.vector_binop_aux i1 i2 lane_op lane_idx num_remaining
                                              lane_width acc s
            = Success (res, s'))
    : R s' m /\ s :< s' /\
      eval s' res
        (Z.lor acc_val
          (SemanticVector.vector_binop_aux v1 v2 binop lane_idx num_remaining (Z.of_N lane_width))).
  Proof using Type.
    revert lane_idx s HR acc acc_val Hacc Hacc_hi res s' H Hv1 Hv2; induction num_remaining as [|n IH]; intros.
    { cbv [SemanticVector.vector_binop_aux SymbolicVector.vector_binop_aux] in *. 
      rewrite Z.lor_0_r. inversion H. subst. eauto. }
    {
      destruct (vector_binop_aux_S_lane_idx _ _ _ _ _ _ _ _ _ _ H)
        as (lane_val & new_acc & s1 & s2 & Hlane & Hins & Hrest).
      eapply make_lane_R in Hlane as (HR1 & Hsubs1 & Heval1); eauto.
      eapply insert_lane_R in Hins as (HR2 & Hsubs2 & Heval2); eauto.
      eapply IH in Hrest as (HR3 & Hsubs3 & Heval3); eauto; clear IH.

      (* Goal 2 first since you need it closed before discharging IH *)
      2: { unfold SemanticVector.insert_lane.
      apply acc_range_preserved; [lia | exact Hacc_hi]. }

      (* Goal 1: combine subsumptions + massage Heval3 *)
      split; [exact HR3|].
      split. solve_subsumed.
      rewrite insert_lane_ldiff_lor in Heval3 by (lia || exact Hacc_hi).
      rewrite <- Z.lor_assoc in Heval3. apply Heval3.
    }
  Qed.
    
  Lemma SymexVectorBinOp_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' 
		(HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src1 src2 : ARG)
    (lane_op : op) (binop : Z -> Z -> Z)
    (Hop : interprets_as_binop lane_op binop)
    (lane_width : N) (Hlw : (lane_width > 0)%N) 
    (H : SymbolicVector.SymexVectorBinOp dst src1 src2 lane_op lane_width s = Success (_tt, s'))
    : exists m',
        SemanticVector.DenoteVectorBinOp sa s_op m dst src1 src2 binop
          (N.to_nat (s_op / lane_width)%N) (Z.of_N lane_width) = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type.
    cbv [SymbolicVector.SymexVectorBinOp] in H. repeat step_symex. cbv [fst snd] in *.
    rename v1 into i1, v2 into i2, HSv1 into Hget1, HSv2 into Hget2.
    eapply (GetOperand_R s m) in Hget1 as (HR0 & Hsubs0 & Heval1); eauto.
    eapply (GetOperand_R s0 m) in Hget2 as (HR1 & Hsubs1 & Heval2); eauto.
    destruct Heval1 as (v1 & Heval1 & Hdenote1); destruct Heval2 as (v2 & Heval2 & Hdenote2).
    
    eapply App_R in HSacc as (HR2 & Hsubs2 & Heval_acc); try eauto. 2: repeat econstructor.
    eapply vector_binop_aux_R in HSresult as (HR3 & Hsubs3 & Heval_res); eauto. rewrite Z.lor_0_l in Heval_res. 
    step_SetOperand. exact Hsa.
    eexists. split; [|split]. 
    { cbv [SemanticVector.DenoteVectorBinOp Crypto.Util.Option.bind].
      rewrite Hdenote1, Hdenote2. exact Hm0. }
    { exact Hs'. }
    { solve_subsumed. }
  Qed.

  (* === Unary vector op lemmas === *)

  Lemma make_unary_lane_R {opts : symbolic_options_computed_opt} {descr : description}
    s m (HR : R s m)
    (i : idx) (v : Z)
    (Hv : eval s i v)
    (lane_op : op) (unaryop : Z -> Z)
    (Hop : interprets_as_unaryop lane_op unaryop)
    (lane_idx : nat) (lane_width : N) (Hlw : (lane_width > 0)%N)
    res s'
    (H : SymbolicVector.make_unary_lane i lane_op lane_idx lane_width s
        = Success (res, s'))
    : R s' m /\ s :< s' /\
      eval s' res (SemanticVector.make_unary_lane v unaryop lane_idx (Z.of_N lane_width)).
  Proof using Type. Admitted.

  Lemma vector_unaryop_aux_S_lane_idx
    {opts : symbolic_options_computed_opt} {descr : description}
    (i : idx) (lane_op : op)
    (lane_idx n : nat) (lane_width : N) (acc : idx) s res s'
    (H : SymbolicVector.vector_unaryop_aux i lane_op lane_idx (S n)
          lane_width acc s = Success (res, s'))
    : exists lane_val new_acc s1 s2,
        SymbolicVector.make_unary_lane i lane_op lane_idx lane_width s
          = Success (lane_val, s1)
    /\ SymbolicVector.insert_lane acc lane_val lane_idx lane_width s1
          = Success (new_acc, s2)
    /\ SymbolicVector.vector_unaryop_aux i lane_op (S lane_idx) n lane_width
          new_acc s2 = Success (res, s').
  Proof using Type. Admitted.

  Lemma vector_unaryop_aux_R {opts : symbolic_options_computed_opt} {descr : description}
        s m (HR : R s m)
        (i : idx) (v : Z)
        (Hv : eval s i v)
        (lane_op : op) (unaryop : Z -> Z)
        (Hop : interprets_as_unaryop lane_op unaryop)
        (lane_idx num_remaining : nat)
        (lane_width : N) (Hlw : (lane_width > 0)%N)
        (acc : idx) (acc_val : Z) (Hacc : eval s acc acc_val)
        (Hacc_hi : Z.shiftr acc_val (Z.of_nat lane_idx * Z.of_N lane_width) = 0)
        res s'
        (H : SymbolicVector.vector_unaryop_aux i lane_op lane_idx num_remaining
                                              lane_width acc s
            = Success (res, s'))
    : R s' m /\ s :< s' /\
      eval s' res
        (Z.lor acc_val
          (SemanticVector.vector_unaryop_aux v unaryop lane_idx num_remaining (Z.of_N lane_width))).
  Proof using Type. Admitted.

  Lemma SymexVectorUnaryOp_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s'
    (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src : ARG)
    (lane_op : op) (unaryop : Z -> Z)
    (Hop : interprets_as_unaryop lane_op unaryop)
    (lane_width : N) (Hlw : (lane_width > 0)%N)
    (H : @SymbolicVector.SymexVectorUnaryOp _ _ s_op sa dst src lane_op lane_width s = Success (_tt, s'))
    : exists m',
        SemanticVector.DenoteVectorUnaryOp sa s_op m dst src unaryop
          (N.to_nat (s_op / lane_width)%N) (Z.of_N lane_width) = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type. Admitted.

  (* === Broadcast lemmas === *)

  Lemma broadcast_aux_R {opts : symbolic_options_computed_opt} {descr : description}
        s m (HR : R s m)
        (lane_val_idx : idx) (lane_val : Z)
        (Hv : eval s lane_val_idx lane_val)
        (lane_idx num_remaining : nat)
        (lane_width : N) (Hlw : (lane_width > 0)%N)
        (acc : idx) (acc_val : Z) (Hacc : eval s acc acc_val)
        (Hacc_hi : Z.shiftr acc_val (Z.of_nat lane_idx * Z.of_N lane_width) = 0)
        res s'
        (H : SymbolicVector.broadcast_aux lane_val_idx lane_idx num_remaining
                                          lane_width acc s
            = Success (res, s'))
    : R s' m /\ s :< s' /\
      eval s' res
        (Z.lor acc_val
          (SemanticVector.broadcast_aux lane_val lane_idx num_remaining (Z.of_N lane_width))).
  Proof using Type. Admitted.

  Lemma broadcast_R {opts : symbolic_options_computed_opt} {descr : description}
        s m (HR : R s m)
        (lane_val_idx : idx) (lane_val : Z)
        (Hv : eval s lane_val_idx lane_val)
        (num_lanes : nat)
        (lane_width : N) (Hlw : (lane_width > 0)%N)
        res s'
        (H : SymbolicVector.broadcast lane_val_idx num_lanes lane_width res s
            = Success (res, s'))
    : R s' m /\ s :< s' /\
      eval s' res (SemanticVector.broadcast lane_val num_lanes (Z.of_N lane_width)).
  Proof using Type. Admitted.

  Lemma mapM_fold_left_R {A} {opts : symbolic_options_computed_opt} {descr : description}
  (f_sym : A -> M unit)
  (f_sem : machine_state -> A -> machine_state)
  (Hstep : forall a s m s',
    R s m -> f_sym a s = Success (tt, s') ->
    R s' (f_sem m a) /\ s :< s')
  : forall l s m s',
    R s m ->
    Symbolic.mapM_ f_sym l s = Success (tt, s') ->
    R s' (fold_left f_sem l m) /\ s :< s'.
  Proof using Type.
    induction l as [|a l IH]; intros s0 m0 s_final HR0 Hsym.
    - cbv [Symbolic.mapM_ Symbolic.mapM] in Hsym.
			step_symex; cbv [fst snd] in *; unfold ret in *.
 			inversion_ErrorT; Prod.inversion_prod; subst.

      cbn [fold_left]. split; [exact HR0 | solve_subsumed].
    - cbn [fold_left].
      cbv [Symbolic.mapM_] in Hsym.
			step_symex.
      cbn [Symbolic.mapM] in HSx.
			repeat step_symex. 
			Admitted.
			(* cbv [ret] in HSx, Hsym. *)
 			(* inversion_ErrorT; Prod.inversion_prod; subst.  *)
			(* destruct b.  *)
			(* edestruct (Hstep _ _ _ _ HR0 HSb) as [HR1 Hsub1]. *)
			(* assert (HSbs' : mapM_ f_sym l s1 = Success (tt, s_final)). *)
			(* { cbv [mapM_ bind ret]. rewrite HSbs. reflexivity. } *)
			(* edestruct (IH _ _ _ HR1 HSbs') as [HR2 Hsub2]. *)
			(* split; [exact HR2 | solve_subsumed]. *)
(* Qed. *)
	

  Lemma interprets_as_add s : interprets_as_binop (add s) (fun a b => Z.land (a + b) (Z.ones (Z.of_N s))).
    Proof. intros a b. cbn [interp_op fold_right]. rewrite Z.add_0_r. reflexivity. Qed.

  Lemma interprets_as_sub s : interprets_as_binop (sub s) (fun a b => Z.land (a - b) (Z.ones (Z.of_N s))).
    Proof. intros a b. cbn [interp_op fold_right].  reflexivity. Qed. 

	Lemma interprets_as_and s : interprets_as_binop (and s) (fun a b => Z.land (Z.land a b) (Z.ones (Z.of_N s))).
    Proof. intros a b. cbn [interp_op fold_right]. f_equal. bitblast.Z.bitblast. Qed.

	Lemma interprets_as_or s : interprets_as_binop (or s) (fun a b => Z.land (Z.lor a b) (Z.ones (Z.of_N s))).
    Proof. intros a b. cbn [interp_op fold_right]. f_equal. bitblast.Z.bitblast. Qed.

  Lemma interprets_as_xor s : interprets_as_binop (xor s) (fun a b => Z.land (Z.lxor a b) (Z.ones (Z.of_N s))).
    Proof. intros a b. cbn [interp_op fold_right]. f_equal. bitblast.Z.bitblast. Qed.

  (* === Per-instruction correctness lemmas === *)

  (* -- BinOp-based instructions -- *)

  Lemma vpaddq_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src1 src2 : ARG)
    (H : SymbolicVector.SymexVectorBinOp dst src1 src2 (add 64%N) 64%N s = Success (_tt, s'))
    : exists m',
        SemanticVector.DenoteVectorBinOp sa s_op m dst src1 src2
          (fun a b => Z.land (a + b) (Z.ones 64)) (N.to_nat (s_op / 64)%N) 64 = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type.
    eapply SymexVectorBinOp_R; try (eassumption || lia). apply interprets_as_add.
  Qed.

  Lemma vpsubq_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src1 src2 : ARG)
    (H : SymbolicVector.SymexVectorBinOp dst src1 src2 (sub 64%N) 64%N s = Success (_tt, s'))
    : exists m',
        SemanticVector.DenoteVectorBinOp sa s_op m dst src1 src2
          (fun a b => Z.land (a - b) (Z.ones 64)) (N.to_nat (s_op / 64)%N) 64 = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type.
    eapply SymexVectorBinOp_R; try (eassumption || lia). apply interprets_as_sub.
  Qed.

  Lemma vpandq_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src1 src2 : ARG)
    (H : SymbolicVector.SymexVectorBinOp dst src1 src2 (and 64%N) 64%N s = Success (_tt, s'))
    : exists m',
        SemanticVector.DenoteVectorBinOp sa s_op m dst src1 src2
          (fun a b => Z.land (Z.land a b) (Z.ones 64)) (N.to_nat (s_op / 64)%N) 64 = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type.
    eapply SymexVectorBinOp_R; try (eassumption || lia). apply interprets_as_and.
  Qed.

  Lemma vporq_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src1 src2 : ARG)
    (H : SymbolicVector.SymexVectorBinOp dst src1 src2 (or 64%N) 64%N s = Success (_tt, s'))
    : exists m',
        SemanticVector.DenoteVectorBinOp sa s_op m dst src1 src2
          (fun a b => Z.land (Z.lor a b) (Z.ones 64)) (N.to_nat (s_op / 64)%N) 64 = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type.
    eapply SymexVectorBinOp_R; try (eassumption || lia). apply interprets_as_or.
  Qed.

  Lemma vpxorq_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src1 src2 : ARG)
    (H : SymbolicVector.SymexVectorBinOp dst src1 src2 (xor 64%N) 64%N s = Success (_tt, s'))
    : exists m',
        SemanticVector.DenoteVectorBinOp sa s_op m dst src1 src2
          (fun a b => Z.land (Z.lxor a b) (Z.ones 64)) (N.to_nat (s_op / 64)%N) 64 = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type.
    eapply SymexVectorBinOp_R; try (eassumption || lia). apply interprets_as_xor.
  Qed.

  Lemma vpaddd_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src1 src2 : ARG)
    (H : SymbolicVector.SymexVectorBinOp dst src1 src2 (add 32%N) 32%N s = Success (_tt, s'))
    : exists m',
        SemanticVector.DenoteVectorBinOp sa s_op m dst src1 src2
          (fun a b => Z.land (a + b) (Z.ones 32)) (N.to_nat (s_op / 32)%N) 32 = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type.
    eapply SymexVectorBinOp_R; try (eassumption || lia). apply interprets_as_add.
  Qed.

  Lemma vpsubd_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src1 src2 : ARG)
    (H : SymbolicVector.SymexVectorBinOp dst src1 src2 (sub 32%N) 32%N s = Success (_tt, s'))
    : exists m',
        SemanticVector.DenoteVectorBinOp sa s_op m dst src1 src2
          (fun a b => Z.land (a - b) (Z.ones 32)) (N.to_nat (s_op / 32)%N) 32 = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type.
    eapply SymexVectorBinOp_R; try (eassumption || lia). apply interprets_as_sub.
  Qed.

  (* -- Non-binop vector instructions -- *)
 Lemma vzeroupper_step_R {opts : symbolic_options_computed_opt} {descr : description}
    (yr : VREG) (s : symbolic_state) (m : machine_state) (s' : symbolic_state)
    (HR : R s m)
    (H : (v <- GetReg (VReg yr);
          lo <- Symbolic.App (slice 0 128, [v]);
          SetReg (VReg yr) lo)%x86symex s = Success (tt, s'))
  : R s' (update_reg_with m
            (fun rs => set_reg rs (VReg yr)
                          (Z.land (get_reg m (VReg yr)) (Z.ones 128))))
    /\ s :< s'.
  Proof using Type. 
				Admitted.
		(* step_GetReg. step_App. step_SetReg subst. *)
  	(* split; [exact Hs' | solve_subsumed]. *)
(* Qed. *)

  Lemma vmovdqu_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src : ARG)
    (H : (v <- GetOperand src;
          Symbolic.SetOperand dst v)%x86symex s = Success (_tt, s'))
    : exists m',
        (v <- DenoteOperand sa s_op m src;
         Semantics.SetOperand sa s_op m dst v)%option = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type. Admitted.

  Lemma vmovq_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src : ARG)
    (H : (v <- GetOperand src;
          v <- Symbolic.App (slice 0 64, [v]);
          Symbolic.SetOperand dst v)%x86symex s = Success (_tt, s'))
    : exists m',
        (v <- DenoteOperand sa 64 m src;
         let v := Z.land v (Z.ones 64) in
         SetOperand sa 64 m dst v)%option = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type. Admitted.

  Lemma vpbroadcastq_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src : ARG)
    (H : (v <- GetOperand src;
          lane <- Symbolic.App (slice 0 64, [v]);
          let num_lanes := N.to_nat (s_op / 64)%N in
          zero <- Symbolic.App (const 0, []);
          result <- SymbolicVector.broadcast_aux lane 0 num_lanes 64%N zero;
          Symbolic.SetOperand dst result)%x86symex s = Success (_tt, s'))
    : exists m',
        (v <- DenoteOperand sa 64 m src;
         let v64 := Z.land v (Z.ones 64) in
         let result := SemanticVector.broadcast v64 (N.to_nat (s_op / 64)%N) 64 in
         Semantics.SetOperand sa s_op m dst result)%option = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type. Admitted.

  Lemma vpblendd_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src1 src2 imm : ARG)
    (H : (v1 <- GetOperand src1;
          v2 <- GetOperand src2;
          imm_val <- GetOperand imm;
          mask <- Symbolic.RevealConst imm_val;
          let num_dwords := N.to_nat (s_op / 32)%N in
          zero <- Symbolic.App (const 0, []);
          result <- SymbolicVector.blend_aux v1 v2 mask 0 num_dwords 32%N zero;
          Symbolic.SetOperand dst result)%x86symex s = Success (_tt, s'))
    : exists m' imm_z,
        (v1 <- DenoteOperand sa s_op m src1;
         v2 <- DenoteOperand sa s_op m src2;
         let result := SemanticVector.blend v1 v2 imm_z (N.to_nat (s_op / 32)%N) 32 in
         Semantics.SetOperand sa s_op m dst result)%option = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type. Admitted.

  Lemma vpmuludq_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src1 src2 : ARG)
    (H : SymbolicVector.SymexMuludq dst src1 src2 s = Success (_tt, s'))
    : exists m',
        (v1 <- DenoteOperand sa s_op m src1;
         v2 <- DenoteOperand sa s_op m src2;
         let result := SemanticVector.muludq_aux v1 v2 0 (N.to_nat (s_op / 64)%N) in
         Semantics.SetOperand sa s_op m dst result)%option = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type. Admitted.

  Lemma vpsrlq_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src imm : ARG)
    (H : SymbolicVector.SymexVectorShiftImm dst src imm (shr 64%N) s = Success (_tt, s'))
    : exists m' imm_z,
        (let lane_shr := (fun v => Z.land (Z.shiftr v imm_z) (Z.ones 64)) in
         SemanticVector.DenoteVectorUnaryOp sa s_op m dst src lane_shr (N.to_nat (s_op / 64)%N) 64)%option = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type. Admitted.

  Lemma vpunpcklqdq_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src1 src2 : ARG)
    (H : (v1 <- GetOperand src1;
          v2 <- GetOperand src2;
          let num_halves := N.to_nat (s_op / 128)%N in
          zero <- Symbolic.App (const 0, []);
          result <- SymbolicVector.unpcklqdq_aux v1 v2 0 num_halves zero;
          Symbolic.SetOperand dst result)%x86symex s = Success (_tt, s'))
    : exists m',
        (v1 <- DenoteOperand sa s_op m src1;
         v2 <- DenoteOperand sa s_op m src2;
         let result := SemanticVector.unpcklqdq_aux v1 v2 0 (N.to_nat (s_op / 128)%N) in
         Semantics.SetOperand sa s_op m dst result)%option = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type. Admitted.

  Lemma vpextrq_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src imm : ARG)
    (H : (v <- GetOperand src;
          imm_val <- GetOperand imm;
          lane <- Symbolic.RevealConst imm_val;
          result <- Symbolic.App (slice (Z.to_N (lane * 64)) 64, [v]);
          Symbolic.SetOperand dst result)%x86symex s = Success (_tt, s'))
    : exists m' lane,
        (v <- DenoteOperand sa 128 m src;
         let result := Z.land (Z.shiftr v (lane * 64)) (Z.ones 64) in
         Semantics.SetOperand sa 64 m dst result)%option = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type. Admitted.

  Lemma vextracti128_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src imm : ARG)
    (H : (v <- GetOperand src;
          imm_val <- GetOperand imm;
          half <- Symbolic.RevealConst imm_val;
          result <- Symbolic.App (slice (Z.to_N (half * 128)) 128, [v]);
          Symbolic.SetOperand dst result)%x86symex s = Success (_tt, s'))
    : exists m' half,
        (v <- DenoteOperand sa 256 m src;
         let result := Z.land (Z.shiftr v (half * 128)) (Z.ones 128) in
         Semantics.SetOperand sa 128 m dst result)%option = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type. Admitted.

  Lemma vinserti128_R {opts : symbolic_options_computed_opt} {descr : description}
    s m _tt s' (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src1 src2 imm : ARG)
    (H : (v1 <- GetOperand src1;
          v2 <- GetOperand src2;
          imm_val <- GetOperand imm;
          half <- Symbolic.RevealConst imm_val;
          result <- Symbolic.App (set_slice (Z.to_N (half * 128)) 128, [v1; v2]);
          Symbolic.SetOperand dst result)%x86symex s = Success (_tt, s'))
    : exists m' half,
        (v1 <- DenoteOperand sa 256 m src1;
         v2 <- DenoteOperand sa 128 m src2;
         let offset := half * 128 in
         let mask := Z.shiftl (Z.ones 128) offset in
         let cleared := Z.land v1 (Z.lnot mask) in
         let result := Z.lor cleared (Z.shiftl (Z.land v2 (Z.ones 128)) offset) in
         Semantics.SetOperand sa 256 m dst result)%option = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type. Admitted.

End WithVectorProofs.
End WithFrame.

Create HintDb vector_proofs.
Hint Resolve vpaddq_R vpsubq_R vpandq_R vporq_R
  vpxorq_R vpaddd_R vpsubd_R vmovdqu_R vmovq_R vpbroadcastq_R vpblendd_R vpmuludq_R vpsrlq_R vpunpcklqdq_R vpextrq_R vextracti128_R vinserti128_R
  : vector_proofs.
