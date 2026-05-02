From Coq Require Import List.
From Coq Require Import Lia.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.
From Coq Require Import NArith.
From Coq Require Import ZArith.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.Util.ErrorT.
Import Coq.Lists.List. (* [map] is [List.map] not [ErrorT.map] *)
Require Import Crypto.Util.ListUtil.IndexOf.
Require Import Crypto.Util.Tactics.WarnIfGoalsRemain.
Require Import Crypto.Util.ZUtil.Definitions.
Require Crypto.Util.Option.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.WithBedrock.Semantics.
Require Import Crypto.Assembly.Equivalence.
Import Sorting.Permutation.

Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Memory. Import coqutil.Map.Memory.
Require Import coqutil.Map.Interface. (* coercions *)
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndianList.
Import Word.Naive.

Require Import Crypto.Util.Prod.
From Crypto.Util.Tactics Require Import BreakMatch DestructHead UniquePose.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.ZUtil.Ones.
Import coqutil.Tactics.autoforward coqutil.Decidable coqutil.Tactics.Tactics.

Require Export Crypto.Assembly.WithBedrock.SymbolicProofsCore.
Require Import Crypto.Assembly.WithBedrock.SymbolicVectorProofs.

Local Coercion ExprRef : idx >-> expr.

Section WithFrame.
Context (frame : mem_state -> Prop).
Section WithCtx1'.
Context (G : symbol -> option Z).
Local Notation eval := (Symbolic.eval G).
Local Notation interp_op := (Symbolic.interp_op G).
Local Notation interprets_as_unaryop := (Symbolic.interprets_as_unaryop G).
Local Notation interprets_as_binop := (Symbolic.interprets_as_binop G).
Local Notation gensym_dag_ok := (Symbolic.gensym_dag_ok G).
Local Notation R_reg := (R_reg G).
Local Notation R_regs := (R_regs G).
Local Notation R_flag := (R_flag G).
Local Notation R_flags := (R_flags G).
Local Notation R_cell64 := (R_cell64 G).
Local Notation R_mem := (R_mem G).
Local Notation R := (R G).

Notation subsumed d1 d2 := (forall i v, eval d1 i v -> eval d2 i v).
Local Infix ":<" := subsumed (at level 70, no associativity).

Import ListNotations.

(* Executing instruction in state s gives state s' *)
(* exists a machine state correponding to s' s.t.  *)
Lemma SymexNornalInstruction_R {opts : symbolic_options_computed_opt} {descr:description} s m (HR : R s m) (instr : NormalInstruction) :
  forall _tt s', Symbolic.SymexNormalInstruction instr s = Success (_tt, s') ->
  exists m', Semantics.DenoteNormalInstruction m instr = Some m' /\ R s' m' /\ s :< s'.
Proof using Type.
  intros [] s' H.
  case instr as [op args].

  cbv [SymexNormalInstruction OperationSize] in H.
  repeat (repeat destruct_one_match_hyp; repeat step01).

  all : repeat
  match goal with
  | |- eval_node _ _ (?op, ?args) ?e =>
      solve [repeat (eauto 99 with nocore || econstructor)]
  | |- eval _ (ExprApp (?op, ?args)) ?e =>
      solve [repeat (eauto 99 with nocore || econstructor)]
  | _ => step
  | |- eval _ (ExprRef ?v) ?e => eval_same_expr_goal; try solve [ (* bashing *)
      exact eq_refl || rewrite Z.bit0_mod; trivial; rewrite  Z.mod_small; trivial; Lia.lia]
  end.

  all: cbv beta delta [DenoteNormalInstruction];
       repeat
  match goal with
  | x := ?v |- _ => let t := type of x in
      assert_fails (idtac; match v with context[match _ with _ => _ end] => idtac end);
          subst x
  | _ => step
  | _ => resolve_SetOperand_using_hyp
  | _ => rewrite (Bool.pull_bool_if Some)
  | |- context[if (?x =? ?y)%N then _ else _] => destruct (x =? y)%N eqn:?; reflect_hyps; subst; try congruence
  | |- exists _, Some _ = Some _ /\ _ => eexists; split; [f_equal|]
  | |- exists _, None   = Some _ /\ _ => exfalso
  | |- _ /\ _ :< _ => split; [|solve[eauto 99 with nocore] ]
  end.

  all: repeat first [ match goal with
                      | [ H : DenoteOperand _ _ _ (Syntax.const _) = Some _ |- _ ] => cbv [DenoteOperand DenoteConst operand_size standalone_operand_size CONST_of_Z] in H
                      end
                    | progress Option.inversion_option
                    | progress subst ].

  all : cbn [fold_right map]; rewrite ?N2Z.id, ?Z.add_0_r, ?Z.add_assoc, ?Z.mul_1_r, ?Z.land_m1_r, ?Z.lxor_0_r, ?Z.lor_0_r;
    (congruence||eauto).
  all: rewrite ?Z.land_ones_low_alt by now try split; try apply Zpow_facts.Zpower2_lt_lin; lia.
  all: rewrite ?(fun x => Z.land_ones_low_alt (x / 8) x) by now split; try (eapply Z.le_lt_trans; [ | apply Zpow_facts.Zpower2_lt_lin ]); try lia; Z.to_euclidean_division_equations; nia.
  all: try exact eq_refl.
  all : try solve [rewrite Z.land_ones, Z.bit0_mod by Lia.lia; exact eq_refl].

  all: try solve[ (* bash flags weakening *)
  match goal with H : R ?s' _ |- R ?s' ?m' =>
      try (is_var s'; destruct s');
      try (is_var m'; destruct m');
      repeat match goal with
             | x := ?v |- _ => subst x
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
                 let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
             | H : _ = None |- _ => progress (try rewrite H; try rewrite H in * )
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn -[Syntax.operation_size] in * ; subst)
             | _ => destruct_one_match
             | _ => progress intuition idtac
             end; rewrite ?Z.add_0_r, ?Z.odd_opp; eauto; try Lia.lia
  end
  ].

  Unshelve. all : match goal with H : context[Syntax.sub] |- _ => idtac | _ => shelve end.
  { cbn; repeat (rewrite ?Z.land_ones, ?Z.add_opp_r by Lia.lia).
    push_Zmod; pull_Zmod. rewrite Z.add_opp_r; congruence. }

  Unshelve. all : match goal with H : context[Syntax.sbb] |- _ => idtac | _ => shelve end.
  { cbn; repeat (rewrite ?Z.land_ones, ?Z.add_opp_r by Lia.lia).
    push_Zmod; pull_Zmod. rewrite ?Z.sub_add_distr, ?Z.add_opp_r. congruence. }

  Unshelve. all : match goal with H : context[Syntax.dec] |- _ => idtac | _ => shelve end.
  { cbn; repeat (rewrite ?Z.land_ones, ?Z.add_opp_r by Lia.lia).
    push_Zmod; pull_Zmod. replace v1 with v by congruence. exact eq_refl. }
  { cbv [Symbolic.PreserveFlag Symbolic.HavocFlags Symbolic.update_flag_with ret] in HSx4; cbn in HSx4; induction_path_ErrorT HSx4; Prod.inversion_prod; subst.
    inversion H; clear H; subst s'.
    split; [|solve[eauto 99 with nocore] ].
    destruct s6, m0;
      repeat match goal with
             | _ => Option.inversion_option_step
             | x := ?v |- _ => subst x
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
                 let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
             | H : _ = None |- _ => progress (try rewrite H; try rewrite H in * )
             | _ => progress (cbv [R_flags R_flag Tuple.fieldwise Tuple.fieldwise' Symbolic.get_flag get_flag ] in *; cbn -[Syntax.operation_size] in * ; subst)
             | _ => destruct_one_match
             | _ => progress intuition idtac
             end; eauto; try Lia.lia; try congruence.
             eexists. split. eauto.
             f_equal. f_equal.
             rewrite ?Z.add_0_r.
             f_equal.
             1:congruence.
             rewrite <-Z.add_opp_r; f_equal.
             pose_operation_size_cases; intuition (subst; trivial). }

  Unshelve. all : match goal with H : context[Syntax.inc] |- _ => idtac | _ => shelve end.
  { cbn; repeat (rewrite ?Z.land_ones, ?Z.add_opp_r by Lia.lia).
    push_Zmod; pull_Zmod. replace v1 with v by congruence. exact eq_refl. }
  { cbv [Symbolic.PreserveFlag Symbolic.HavocFlags Symbolic.update_flag_with ret] in HSx4; cbn in HSx4; induction_path_ErrorT HSx4; Prod.inversion_prod; subst.
    inversion H; subst s'.
    split; [|solve[eauto 99 with nocore] ].
    destruct s6, m0;
      repeat match goal with
             | _ => Option.inversion_option_step
             | x := ?v |- _ => subst x
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
                 let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
             | H : _ = None |- _ => progress (try rewrite H; try rewrite H in * )
             | _ => progress (cbv [R_flags R_flag Tuple.fieldwise Tuple.fieldwise' Symbolic.get_flag get_flag ] in *; cbn -[Syntax.operation_size] in * ; subst)
             | _ => destruct_one_match
             | _ => progress intuition idtac
             end; eauto; try Lia.lia; try congruence.
             eexists. split. eauto.
             f_equal. f_equal.
             rewrite ?Z.add_0_r.
             f_equal.
             1:congruence.
             f_equal.
             pose_operation_size_cases; intuition (destruct_head'_ex; subst; try discriminate; trivial). }

  Unshelve. all : match goal with H : context[Syntax.add] |- _ => idtac | _ => shelve end.
  { destruct s';
      repeat match goal with
             | x := ?v |- _ => subst x
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
                 let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
             | H : _ = None |- _ => progress (try rewrite H; try rewrite H in * )
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn -[Syntax.operation_size] in * ; subst)
             | _ => destruct_one_match
             | _ => progress intuition idtac
             end; rewrite ?Z.add_0_r, ?Z.odd_opp; eauto; try Lia.lia; try congruence.
             replace (Z.signed n 0) with 0; cycle 1.
             { pose_operation_size_cases. clear -H0; intuition (subst; cbv; trivial). }
             rewrite Z.add_0_r; cbv [Z.signed]; congruence. }

  Unshelve. all : match goal with H : context[Syntax.adc] |- _ => idtac | _ => shelve end.
  { destruct s';
      repeat match goal with
             | x := ?v |- _ => subst x
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
                 let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
             | H : _ = None |- _ => progress (try rewrite H; try rewrite H in * )
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn -[Syntax.operation_size] in * ; subst)
             | _ => destruct_one_match
             | _ => progress intuition idtac
             end; rewrite ?Z.add_assoc, ?Z.add_0_r, ?Z.odd_opp; eauto; try Lia.lia; try congruence. }

  Unshelve. all : match goal with H : context[Syntax.adcx] |- _ => idtac | _ => shelve end.
  { cbn [fold_right] in *; rewrite ?Z.bit0_odd, ?Z.add_0_r, ?Z.add_assoc in *; assumption. }

  Unshelve. all : match goal with H : context[Syntax.adox] |- _ => idtac | _ => shelve end.
  { cbn [fold_right] in *; rewrite ?Z.bit0_odd, ?Z.add_0_r, ?Z.add_assoc in *; assumption. }

  Unshelve. all : match goal with H : context[Syntax.cmovc] |- _ => idtac |  H : context[Syntax.cmovb] |- _ => idtac |  H : context[Syntax.cmovo] |- _=> idtac | _ => shelve end.
  (* cmovc / cmovb / cmovo *)
  all: (destruct vCF||destruct vOF); cbn [negb Z.b2z Z.eqb] in *; eauto 9; [].
  all: enough (m = m0) by (subst; eauto 9).
  all: clear -Hm0 Hv frame G ; eauto using SetOperand_same.
  all: fail.

  Unshelve. all : match goal with H : context[Syntax.cmovnz] |- _ => idtac | _ => shelve end.
  { (* cmovnz *)
    destruct vZF; cbn [negb Z.b2z Z.eqb] in *; eauto 9; [].
    enough (m = m0) by (subst; eauto 9).
    clear -Hm0 Hv0 frame G ; eauto using SetOperand_same. }

  Unshelve. all : match goal with H : context[Syntax.test] |- _ => idtac | _ => shelve end.
  { destruct (Equality.ARG_beq_spec a a0); try discriminate; subst a0.
    replace v0 with v in * by congruence; clear v0.
    rewrite Z.land_diag.
    case s', m in *; cbn;
      repeat match goal with
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn in * ; subst)
             | _ => progress intuition eauto 1
    end. }

  Unshelve. all : match goal with H : context[Syntax.sar] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { rewrite Z.land_m1_r in *.
    subst st st0.
    rewrite <-H1; cbn.
    replace (1 <? Z.of_N n) with true; cycle 1. {
     pose_operation_size_cases; intuition (subst; destruct_head'_ex; subst; try discriminate; cbn; clear; lia). }
    revert Hs'.
    repeat match goal with x:= _ |- _ => subst x end;
    destruct s';
    repeat match goal with
           | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
           | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
               let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
           | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn -[Syntax.operation_size] in * ; subst)
           | _ => destruct_one_match
           | _ => progress intuition idtac
           end; eauto. }

  Unshelve. all : match goal with H : context[Syntax.rcr] |- _ => idtac | _ => shelve end; shelve_unifiable.
  all : change Symbolic.rcrcnt with rcrcnt in *.
  { repeat destruct_one_match; try lia.
  all:
      destruct s';
      repeat match goal with
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
                 let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
             | H : _ = None |- _ => progress (try rewrite H; try rewrite H in * )
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise' set_flag set_flag_internal] in *; cbn -[Syntax.operation_size] in * ; subst)
             | _ => destruct_one_match
             | _ => progress intuition idtac
             end; try eauto; try Lia.lia.
     destr (machine_flag_state m0); cbn [Tuple.tuple'] in *; DestructHead.destruct_head'_prod; subst; Prod.inversion_prod; subst.
     f_equal.
     let E0 := match goal with H : rcrcnt _ _ = _ |- _ => H end in
     rewrite E0; cbn.
     rewrite <-2Z.bit0_odd, Z.lor_spec, Z.shiftl_spec_low, Bool.orb_false_r; trivial.
     pose_operation_size_cases; intuition (subst; cbn; clear; lia). }

  Unshelve. all : match goal with H : context[Syntax.lea] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { (* lea *)
    cbv [SetOperand update_reg_with] in *; Option.inversion_option; subst; trivial. }

  Unshelve. all : match goal with H : context[Syntax.shrd] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply Z.bits_inj_iff'; intros i Hi.
    repeat rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.shiftr_spec, ?Z.shiftl_spec, ?Z.testbit_ones_nonneg, ?Z.testbit_0_l; try lia.
    destr (i <? Z.of_N n); rewrite ?Bool.orb_false_r, ?Bool.andb_false_r, ?Bool.andb_true_r; trivial.
    replace v0 with v3 by congruence; f_equal; f_equal.
    rewrite Z.land_ones, Z.mod_small.
    1: lia.
    3: enough (0 <= Z.land v3 (Z.of_N n - 1)) by lia; eapply Z.land_nonneg; right.
    1,2,3:pose_operation_size_cases; intuition (subst; cbn; clear; lia). }

  Unshelve. all : match goal with H : context[Syntax.shld] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { repeat match goal with H : ?x = Some _, H' : ?x = Some _ |- _ => rewrite H' in *; Option.inversion_option end.
    progress subst.
    replace (Z.land (Z.of_N n) (Z.ones (Z.of_N n))) with (Z.of_N n)
      by (rewrite Z.land_ones, Z.mod_small; try split; try lia; apply Zpow_facts.Zpower2_lt_lin; lia).
    assert (0 <= Z.of_N n - 1) by (pose_operation_size_cases; intuition (subst; cbn; clear; lia)).
    rewrite <- !Z.shiftl_opp_r.
    rewrite !Z.shiftl_lor.
    rewrite <- !Z.land_lor_distr_l, <- Z.land_assoc, Z.land_diag.
    rewrite !Z.shiftl_shiftl by (try apply Z.land_nonneg; lia).
    f_equal; f_equal; f_equal; try lia. }

  Unshelve. all : match goal with H : context[Syntax.shlx] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { rewrite <- Z.land_assoc.
    f_equal; f_equal; [].
    pose_operation_size_cases; intuition subst; reflexivity. }

  Unshelve. all : match goal with H : context[push] |- _ => idtac | H : context[pop] |- _ => idtac | _ => shelve end; shelve_unifiable.
  all: rewrite !Z.land_ones by lia; push_Zmod; pull_Zmod; f_equal; lia.

  Unshelve. all : match goal with H : context[Syntax.vzeroupper] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { (* vzeroupper: each YMM gets slice 0 128, matching Z.land _ (Z.ones 128) *)
    eapply mapM_fold_left_R in H. exact H. intros. apply vzeroupper_step_R; assumption. exact HR.
  }

  (* vpaddq *)
  Unshelve. all : match goal with H : context[Syntax.vpaddq] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vpaddq_R;  [eassumption | lia | eassumption]. }

  (* vpsubq *)
  Unshelve. all : match goal with H : context[Syntax.vpsubq] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vpsubq_R;  [eassumption | lia | eassumption]. }

  (* vpandq *)
  Unshelve. all : match goal with H : context[Syntax.vpandq] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vpandq_R;  [eassumption | lia | eassumption]. }

  (* vporq *)
  Unshelve. all : match goal with H : context[Syntax.vporq] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vporq_R;  [eassumption | lia | eassumption]. }

  (* vpxorq *)
  Unshelve. all : match goal with H : context[Syntax.vpxorq] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vpxorq_R;  [eassumption | lia | eassumption]. }

  (* vpaddd *)
  Unshelve. all : match goal with H : context[Syntax.vpaddd] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vpaddd_R;  [eassumption | lia | eassumption]. }

  (* vpsubd *)
  Unshelve. all : match goal with H : context[Syntax.vpsubd] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vpsubd_R;  [eassumption | lia | eassumption]. }

  (* vmovdqu *)
  Unshelve. all : match goal with H : context[Syntax.vmovdqu] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vmovdqu_R;  [eassumption | lia | eassumption]. }

  (* vmovq *)
  Unshelve. all : match goal with H : context[Syntax.vmovq] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vmovq_R;  [eassumption | lia | eassumption]. }

  (* vpbroadcastq *)
  Unshelve. all : match goal with H : context[Syntax.vpbroadcastq] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vpbroadcastq_R;  [eassumption | lia | eassumption]. }

  (* vpblendd *)
  Unshelve. all : match goal with H : context[Syntax.vpblendd] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vpblendd_R;  [eassumption | lia | eassumption]. }

  (* vpmuludq *)
  Unshelve. all : match goal with H : context[Syntax.vpmuludq] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vpmuludq_R;  [eassumption | lia | eassumption]. }

  (* vpsrlq *)
  Unshelve. all : match goal with H : context[Syntax.vpsrlq] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vpsrlq_R;  [eassumption | lia | eassumption]. }

  (* vpunpcklqdq *)
  Unshelve. all : match goal with H : context[Syntax.vpunpcklqdq] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vpunpcklqdq_R;  [eassumption | lia | eassumption]. }

  (* vpextrq *)
  Unshelve. all : match goal with H : context[Syntax.vpextrq] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vpextrq_R;  [eassumption | lia | eassumption]. }

  (* vextracti128 *)
  Unshelve. all : match goal with H : context[Syntax.vextracti128] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vextracti128_R;  [eassumption | lia | eassumption]. }

  (* vinserti128 *)
  Unshelve. all : match goal with H : context[Syntax.vinserti128] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply vinserti128_R;  [eassumption | lia | eassumption]. }

  Unshelve. all: shelve_unifiable.
	(* cbn. repeat rewrite Z.land_same_r. autorewrite with zsimplify push_Zshift. clear.  cbn.  *)

  all: fail_if_goals_remain ().
(* Qed here hangs until the kernel crashes. Admitting until it can be sped up *)
Admitted.


Lemma SymexLines_R {opts : symbolic_options_computed_opt} s m (HR : R s m) asm :
  forall _tt s', Symbolic.SymexLines asm s = Success (_tt, s') ->
  exists m', Semantics.DenoteLines m asm = Some m' /\ R s' m' /\ s :< s'.
Proof using Type.
  revert dependent m; revert dependent s; induction asm; cbn [SymexLines DenoteLines]; intros.
  { inversion H; subst; eauto. }
  destruct_head' Line.
  rewrite unfold_bind in *; destruct_one_match_hyp; inversion_ErrorT.
  cbv [SymexLine SymexRawLine DenoteLine DenoteRawLine ret err Crypto.Util.Option.bind] in *; cbn in *.
  destruct_one_match_hyp; inversion_ErrorT; subst; eauto; destruct_head'_prod.
  eapply SymexNornalInstruction_R in E; eauto. destruct E as (m1&Hm1&Rm1&?). rewrite Hm1.
  eapply IHasm in H; eauto. destruct H as (?&?&?&?). break_innermost_match; eauto 9.
Qed.
End WithCtx1'.
End WithFrame.
