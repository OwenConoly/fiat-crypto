Require Crypto.Assembly.Parse.
Require Import Coq.Program.Tactics.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.Orders.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.FSets.FMapFacts.
Require Crypto.Util.Tuple.
Require Import Util.OptionList.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Hints.ZArith.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ZUtil.Ones.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Strings.Subscript.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.Structures.Equalities.Iso.
Require Import Crypto.Util.Structures.Equalities.Prod.
Require Import Crypto.Util.Structures.Equalities.Option.
Require Import Crypto.Util.Structures.Orders.Iso.
Require Import Crypto.Util.Structures.Orders.Prod.
Require Import Crypto.Util.Structures.Orders.Option.
Require Import Crypto.Util.Structures.OrdersEx.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.Concat.
Require Import Crypto.Util.ListUtil.GroupAllBy.
Require Import Crypto.Util.ListUtil.FoldMap. Import FoldMap.List.
Require Import Crypto.Util.ListUtil.IndexOf. Import IndexOf.List.
Require Import Crypto.Util.ListUtil.Forall.
Require Import Crypto.Util.ListUtil.Permutation.
Require Import Crypto.Util.ListUtil.Partition.
Require Import Crypto.Util.ListUtil.Filter.
Require Import Crypto.Util.ListUtil.PermutationCompat. Import ListUtil.PermutationCompat.Coq.Sorting.Permutation.
Require Import Crypto.Util.NUtil.Sorting.
Require Import Crypto.Util.NUtil.Testbit.
Require Import Crypto.Util.FSets.FMapOption.
Require Import Crypto.Util.FSets.FMapN.
Require Import Crypto.Util.FSets.FMapZ.
Require Import Crypto.Util.FSets.FMapProd.
Require Import Crypto.Util.FSets.FMapIso.
Require Import Crypto.Util.FSets.FMapSect.
Require Import Crypto.Util.FSets.FMapInterface.
Require Import Crypto.Util.FSets.FMapFacts.
Require Import Crypto.Util.FSets.FMapTrieEx.
Require Import Crypto.Util.MSets.MSetN.
Require Import Crypto.Util.ListUtil.PermutationCompat.
Require Import Crypto.Util.Bool.LeCompat.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeUnderBindersBy.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.ZUtil.Lxor.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.Tactics.WarnIfGoalsRemain.
Require Import Crypto.Util.Bool.Reflect.
Require Import coqutil.Z.bitblast.
Require Import Coq.Strings.String Crypto.Util.Strings.Show.
Require Import Crypto.Assembly.Syntax.
Import ListNotations.
Definition idx := N.
Local Set Decidable Equality Schemes.
Definition symbol := N.

Class OperationSize := operation_size : N.
Global Instance Show_OperationSize : Show OperationSize := show_N.

Section S.
Implicit Type s : OperationSize.
Variant op := old s (_:symbol) | const (_ : Z) | add s | addcarry s | subborrow s | addoverflow s | neg s | shl s | shr s | sar s | rcr s | and s | or s | xor s | slice (lo sz : N) | mul s | set_slice (lo sz : N) | selectznz | iszero (* | ... *)
  | addZ | mulZ | negZ | shlZ | shrZ | andZ | orZ | xorZ | addcarryZ s | subborrowZ s.
Definition op_beq a b := if op_eq_dec a b then true else false.
End S.

Global Instance Show_op : Show op := fun o =>
  match o with
  | old s n => "old " ++ show s ++ " " ++ show n
  | const n => "const " ++ show n
  | add s => "add " ++ show s
  | addcarry s => "addcarry " ++ show s
  | subborrow s => "subborrow " ++ show s
  | addoverflow s => "addoverflow " ++ show s
  | neg s => "neg " ++ show s
  | shl s => "shl " ++ show s
  | shr s => "shr " ++ show s
  | sar s => "sar " ++ show s
  | rcr s => "rcr " ++ show s
  | and s => "and " ++ show s
  | or s => "or " ++ show s
  | xor s => "xor " ++ show s
  | slice lo sz => "slice " ++ show lo ++ " " ++ show sz
  | mul s => "mul " ++ show s
  | set_slice lo sz => "set_slice " ++ show lo ++ " " ++ show sz
  | selectznz => "selectznz"
  | iszero => "iszero"
  | addZ => "addZ"
  | mulZ => "mulZ"
  | negZ => "negZ"
  | shlZ => "shlZ"
  | shrZ => "shrZ"
  | andZ => "andZ"
  | orZ => "orZ"
  | xorZ => "xorZ"
  | addcarryZ s => "addcarryZ " ++ show s
  | subborrowZ s => "subborrowZ " ++ show s
  end%string.

Definition show_op_subscript : Show op := fun o =>
  match o with
  | old s n => "old" ++ String.to_subscript (show s) ++ " " ++ show n
  | const n => "const " ++ show n
  | add s => "add" ++ String.to_subscript (show s)
  | addcarry s => "addcarry" ++ String.to_subscript (show s)
  | subborrow s => "subborrow" ++ String.to_subscript (show s)
  | addoverflow s => "addoverflow" ++ String.to_subscript (show s)
  | neg s => "neg" ++ String.to_subscript (show s)
  | shl s => "shl" ++ String.to_subscript (show s)
  | shr s => "shr" ++ String.to_subscript (show s)
  | sar s => "sar" ++ String.to_subscript (show s)
  | rcr s => "rcr" ++ String.to_subscript (show s)
  | and s => "and" ++ String.to_subscript (show s)
  | or s => "or" ++ String.to_subscript (show s)
  | xor s => "xor" ++ String.to_subscript (show s)
  | slice lo sz => "slice" ++ String.to_subscript (show lo) ++ "," ++ String.to_subscript (show sz)
  | mul s => "mul" ++ String.to_subscript (show s)
  | set_slice lo sz => "set_slice" ++ String.to_subscript (show lo) ++ "," ++ String.to_subscript (show sz)
  | selectznz => "selectznz"
  | iszero => "iszero"
  | addZ => "addℤ"
  | mulZ => "mulℤ"
  | negZ => "negℤ"
  | shlZ => "shlℤ"
  | shrZ => "shrℤ"
  | andZ => "andℤ"
  | orZ => "orℤ"
  | xorZ => "xorℤ"
  | addcarryZ s => "addcarryℤ" ++ String.to_subscript (show s)
  | subborrowZ s => "subborrowℤ" ++ String.to_subscript (show s)
  end%string.

Module FMapOp.
  Definition op_args : Set := (option OperationSize * (option symbol * (option Z * (option N * option N)))).
  Definition op' : Set := N * op_args.
  Definition eta_op_cps {T} (k : op -> T) (o : op) : T.
  Proof.
    pose o as o'.
    destruct o.
    all: let v := (eval cbv [o'] in o') in
         exact (k v).
  Defined.

  Definition nat_of_op (o : op) : nat.
  Proof.
    evar (base : nat).
    destruct o.
    all: let rec peel_S val :=
           lazymatch val with
           | S ?val => apply S; peel_S val
           | ?ev => is_evar ev;
                    let __ := open_constr:(eq_refl : ev = S _) in
                    exact O
           end in
         let v := (eval cbv [base] in base) in
         peel_S v.
    Unshelve.
    exact O.
  Defined.

  Definition args_of_op (o : op) : op_args.
  Proof.
    destruct o; hnf.
    all: repeat lazymatch reverse goal with
                | [ H : ?T |- ?A * ?B ]
                  => lazymatch A with
                     | context[option T]
                       => split; [ | clear H ]
                     | _ => split; [ repeat apply pair; exact None | ]
                     end
                | [ H : ?T |- _ ]
                  => lazymatch goal with
                     | [ |- option T ] => exact (Some H)
                     | [ |- _ ] => idtac "bad"
                     end
                | [ |- _ * _ ] => split
                | [ |- option _ ] => exact None
                end.
  Defined.

  Definition op'_of_op : op -> op'
    := Eval compute in eta_op_cps (fun o => (N.of_nat (nat_of_op o), args_of_op o)).

  Derive op_of_op'_opt
         SuchThat ((forall (o : op), op_of_op'_opt (op'_of_op o) = Some o)
                   /\ (forall (n n' : op'), option_map op'_of_op (op_of_op'_opt n) = Some n' -> n = n'))
         As op_op'_correct.
  Proof.
    instantiate (1:=ltac:(intros [n v]; hnf in v; destruct_head'_prod; destruct n as [|n])) in (value of op_of_op'_opt).
    subst op_of_op'_opt.
    split.
    { intro o; destruct o; cbv [op'_of_op].
      all: [ > cbv beta iota;
             lazymatch goal with
             | [ |- ?ev = Some _ ]
               => is_evar ev;
                  let H := fresh in
                  pose ev as H;
                  instantiate (1:=ltac:(lazymatch goal with
                                        | [ n : positive |- _ ]
                                          => destruct n
                                        | _ => idtac
                                        end)) in (value of H);
                  subst H; cbv beta iota
             end .. ].
      all: lazymatch goal with
           | [ |- ?ev = Some ?v ]
             => is_evar ev;
                let h := head v in
                let H := fresh in
                pose ev as H;
                instantiate (1:=ltac:(reverse)) in (value of H);
                subst H;
                repeat match goal with
                       | [ |- context[?ev ?x] ]
                         => is_evar ev;
                            let H := fresh in
                            pose ev as H;
                            lazymatch x with
                            | Some _
                              => instantiate (1:=ltac:(let x := fresh "x" in intro x; intros; destruct x; [ reverse | exact None ])) in (value of H)
                            | None
                              => instantiate (1:=ltac:(let x := fresh "x" in intro x; intros; destruct x; [ exact None | reverse ])) in (value of H)
                            | ?x
                              => tryif is_var x
                                then instantiate (1:=ltac:(intro)) in (value of H)
                                else idtac "unknown" x
                            end;
                            subst H; cbv beta iota
                       end;
                reflexivity
           end. }
    { intros [n nargs] [n' nargs'].
      set (f := option_map _).
      break_innermost_match.
      all: let G := lazymatch goal with |- ?G => G end in
           tryif has_evar G then instantiate (1:=None) else idtac.
      all: vm_compute.
      all: lazymatch goal with
           | [ |- Some _ = Some _ -> _ ] => intro; inversion_option; inversion_pair; subst; try reflexivity
           | [ |- None = Some _ -> _ ] => let H := fresh in intro H; exfalso; clear -H; inversion_option
           end. }
  Qed.

  Module OptionNMap <: S := OptionUsualMap NMap.
  Module OptionZMap <: S := OptionUsualMap ZMap.
  Module OptionSymbolMap <: S := OptionNMap.
  Module OptionOperationSizeMap <: S := OptionNMap.
  Module OpArgsMap0 <: S := OptionNMap.
  Module OpArgsMap1 <: S := ProdUsualMap OptionNMap OpArgsMap0.
  Module OpArgsMap2 <: S := ProdUsualMap OptionZMap OpArgsMap1.
  Module OpArgsMap3 <: S := ProdUsualMap OptionSymbolMap OpArgsMap2.
  Module OpArgsMap4 <: S := ProdUsualMap OptionOperationSizeMap OpArgsMap3.
  Module OpArgsMap <: S := OpArgsMap4.
  Module OpMap' <: S := ProdUsualMap NMap OpArgsMap.
  Module OpSectOp' <: SectMiniOrderedType OpMap'.E.
    Definition t := op.
    Include HasUsualEq.
    Include UsualIsEq.
    Include UsualIsEqOrig.
    Definition to_ : t -> OpMap'.E.t := Eval vm_compute in op'_of_op.
    Definition of_ (v : OpMap'.E.t) : t
      := Eval vm_compute in match op_of_op'_opt v with
                            | Some v => v
                            | None => old 0%N 0%N
                            end.
    Global Instance Proper_to_ : Proper (Logic.eq ==> Logic.eq) to_ | 5.
    Proof. repeat intro; subst; reflexivity. Qed.
    Global Instance Proper_of_ : Proper (Logic.eq ==> Logic.eq) of_ | 5.
    Proof. repeat intro; subst; reflexivity. Qed.
    Lemma of_to : forall x, eq (of_ (to_ x)) x.
    Proof.
      intro x.
      refine (_ : match op_of_op'_opt (op'_of_op x) with
                  | Some v => v
                  | None => _
                  end = x).
      rewrite (proj1 op_op'_correct).
      reflexivity.
    Qed.
    Include LiftIsoHasLt OpMap'.E.
    Include LiftSectHasMiniOrderedType OpMap'.E.
    Include LiftSectIsLt OpMap'.E.
  End OpSectOp'.
  Module OpMap <: UsualS := SectS OpMap' OpSectOp'.
End FMapOp.

Module OpMap := FMapOp.OpMap.

Definition associative o := match o with add _|mul _|mulZ|or _|and _|xor _|andZ|orZ|xorZ=> true | _ => false end.
Definition commutative o := match o with add _|addcarry _|addoverflow _|mul _|mulZ|or _|and _|xor _|andZ|orZ|xorZ => true | _ => false end.
Definition identity o := match o with mul N0 => Some 0%Z| mul _|mulZ=>Some 1%Z |add _|addZ|or _|orZ|xor _|xorZ|addcarry _|addcarryZ _|addoverflow _ => Some 0%Z | and s => Some (Z.ones (Z.of_N s))|andZ => Some (-1)%Z |_=> None end.
Definition sum o := match o with add _|addZ => true | _ => false end.
(* identity, but not in the first slot *)
Definition identity_after_0 o := match o with subborrow _|subborrowZ _ => Some 0%Z | _=> None end.
Definition unary_truncate_size o := match o with add s|and s|or s|xor s|mul s => Some (Z.of_N s) | addZ|mulZ|andZ|orZ|xorZ => Some (-1)%Z | _ => None end.
Definition op_always_interps o := match o with add _|addcarry _|addoverflow _|and _|or _|xor _|mul _|addZ|mulZ|andZ|orZ|xorZ|addcarryZ _ => true | _ => false end.
Definition combines_to o := match o with add s => Some (mul s) | addZ => Some mulZ | _ => None end.

Definition node (A : Set) : Set := op * list A.
Global Instance Show_node {A : Set} {show_A : Show A} : Show (node A) := show_prod.

Local Unset Elimination Schemes.
Inductive expr : Set :=
| ExprRef (_ : idx)
| ExprApp (_ : node expr).

Print List.foldmap.

Compute (node expr).
Print op.

Local Set Elimination Schemes.
Section expr_ind.
  Context (P : expr -> Prop)
    (HRef : forall i, P (ExprRef i))
    (HApp : forall n, Forall P (snd n) -> P (ExprApp n)).
  Fixpoint expr_ind e {struct e} : P e :=
    match e with
    | ExprRef i => HRef i
    | ExprApp n => HApp _ (list_rect _ (Forall_nil _) (fun e _ H => Forall_cons e (expr_ind e) H) (snd n))
    end.
End expr_ind.
Definition invert_ExprRef (e : expr) : option idx :=
  match e with ExprRef i => Some i | _ => None end.
Definition Show_expr_body (Show_expr : Show expr) : Show expr
  := Eval cbv -[String.append show_N concat List.map Show_op] in
      fun e => match e with
               | ExprRef i => "ExprRef " ++ show i
               | ExprApp (o, e) => "ExprApp " ++ show (o, e)
               end%string.
Definition Show_expr : Show expr
  := Eval cbv -[String.append show_N concat List.map Show_op] in
      fix Show_expr e := Show_expr_body Show_expr e.
Global Existing Instance Show_expr.

Local Notation max_powers_of_two := 5%nat (only parsing).
Local Notation max_decimal := 256%Z (only parsing).

Definition show_infix_op (o : op) : option string
  := match o with
     | add s => Some ("+" ++ String.to_subscript (show s))
     | shl s => Some (">>" ++ String.to_subscript (show s))
     | shr s => Some (">>" ++ String.to_subscript (show s))
     | and s => Some ("&"  ++ String.to_subscript (show s))
     | or s  => Some ("|"  ++ String.to_subscript (show s))
     | xor s => Some ("^"  ++ String.to_subscript (show s))
     | mul s => Some ("*"  ++ String.to_subscript (show s))
     | sar s => Some (">>>" ++ String.to_subscript (show s))
     | addZ  => Some "+ℤ"
     | mulZ  => Some "*ℤ"
     | shlZ  => Some "<<ℤ"
     | shrZ  => Some ">>ℤ"
     | andZ  => Some "&ℤ"
     | orZ   => Some "|ℤ"
     | xorZ  => Some "^ℤ"
     | _ => None
     end%string.

Definition show_prefix_op (o : op) : option (string * Level)
  := match o with
     | neg s => Some ("-" ++ String.to_subscript (show s), opp_lvl)
     | negZ => Some ("-ℤ", opp_lvl)
     | _ => None
     end%string.

Definition show_lvl_expr_pretty : ShowLevel expr
  := fix show_lvl_pretty_expr (e : expr) : Level -> string
    := let __ : ShowLevel expr := show_lvl_pretty_expr in
       let __ : Show expr := @Show_of_ShowLevel _ show_lvl_pretty_expr in
       let show_comment_args args
         := match args with
            | nil => ""
            | _ => " (* " ++ show args ++ " *)"
            end%string in
       match e with
       | ExprRef i => fun _ => "#" ++ show i
       | ExprApp (old s x, args) => lvl_wrap_parens app_lvl ("old" ++ String.to_subscript (show s) ++ " " ++ show x ++ show_comment_args args)
       | ExprApp (const x, args) => fun lvl => PowersOfTwo.show_lvl_Z_up_to max_powers_of_two max_decimal x lvl ++ show_comment_args args
       | ExprApp ((add _|shl _|shr _|and _|or _|xor _|mul _|sar _|addZ|mulZ|shlZ|shrZ|andZ|orZ|xorZ) as o, args)
         => let o : string := Option.invert_Some (show_infix_op o) in
            match args with
            | nil => fun _ => o ++ "[]"
            | x :: nil => fun _ => o ++ "[" ++ show x ++ "]"
            | _ => fun _ => "(" ++ String.concat (" " ++ o ++ " ") (List.map show args) ++ ")"
            end
       | ExprApp ((neg _|negZ) as o, args)
         => let '(o, lvl) := Option.invert_Some (show_prefix_op o) in
            match args with
            | nil => fun _ => o ++ "[]"
            | x :: nil => fun _ => o ++ show_lvl x lvl
            | _ => fun _ => o ++ show args
            end
       | ExprApp (o, args)
         => fun _ => "(" ++ show_op_subscript o ++ ", " ++ show args ++ ")"
       end%string%list.

Definition show_expr_pretty : Show expr
  := @Show_of_ShowLevel _ show_lvl_expr_pretty.

Lemma op_beq_spec a b : BoolSpec (a=b) (a<>b) (op_beq a b).
Proof using Type. cbv [op_beq]; destruct (op_eq_dec a b); constructor; congruence. Qed.
Global Instance reflect_eq_op : reflect_rel eq op_beq | 10 := reflect_rel_of_BoolSpec op_beq_spec.
Fixpoint expr_beq (X Y : expr) {struct X} : bool :=
  match X, Y with
  | ExprRef x, ExprRef x0 => N.eqb x x0
  | ExprApp x, ExprApp x0 =>
      Prod.prod_beq _ _ op_beq (ListUtil.list_beq expr expr_beq) x x0
  | _, _ => false
  end.
Lemma expr_beq_spec a b : BoolSpec (a=b) (a<>b) (expr_beq a b).
Proof using Type.
  revert b; induction a, b; cbn.
  1: destruct (N.eqb_spec i i0); constructor; congruence.
  1,2: constructor; congruence.
  destruct n, n0; cbn.
  destruct (op_beq_spec o o0); cbn in *; [subst|constructor; congruence].
  revert l0; induction H, l0; cbn; try (constructor; congruence); [].
  destruct (H e); cbn; try (constructor; congruence); []; subst.
  destruct (IHForall l0); [left|right]; congruence.
Qed.
Global Instance reflect_eq_expr : reflect_rel eq expr_beq | 10 := reflect_rel_of_BoolSpec expr_beq_spec.
Lemma expr_beq_true a b : expr_beq a b = true -> a = b.
Proof using Type. destruct (expr_beq_spec a b); congruence. Qed.

Require Import Crypto.Util.Option Crypto.Util.Notations Coq.Lists.List.
Import ListNotations.

Section WithContext.
  Context (ctx : symbol -> option Z).
  Definition signed s n : Z := (Z.land (Z.shiftl 1 (Z.of_N s-1) + n) (Z.ones (Z.of_N s)) - Z.shiftl 1 (Z.of_N s-1))%Z.
  Definition interp_op o (args : list Z) : option Z :=
    let keep n x := Z.land x (Z.ones (Z.of_N n)) in
    match o, args with
    | old s x, nil => match ctx x with Some v => Some (keep s v) | None => None end
    | const z, nil => Some z
    | add s, args => Some (keep s (List.fold_right Z.add 0 args))
    | addcarry s, args =>
        Some (Z.shiftr (List.fold_right Z.add 0 args) (Z.of_N s) mod 2)
    | subborrow s, cons a args' =>
        Some ((- Z.shiftr (a - List.fold_right Z.add 0 args') (Z.of_N s)) mod 2)
    | addoverflow s, args => Some (Z.b2z (negb (Z.eqb
      (signed s (keep s (List.fold_right Z.add 0 args)))
                         (List.fold_right Z.add 0%Z (List.map (signed s) args)))))
    | neg s, [a] => Some (keep s (- a))
    | shl s, [a; b] => Some (keep s (Z.shiftl a b))
    | shr s, [a; b] => Some (keep s (Z.shiftr a b))
    | sar s, [a; b] => Some (keep s (Z.shiftr (signed s a) b))
    | rcr s, [v1; cf; cnt] => Some (
        let v1c := Z.lor v1 (Z.shiftl cf (Z.of_N s)) in
        let l := Z.lor v1c (Z.shiftl v1 (1+Z.of_N s)) in
        keep s (Z.shiftr l cnt))
    | and s, args => Some (keep s (List.fold_right Z.land (-1) args))
    | or s, args => Some (keep s (List.fold_right Z.lor 0 args))
    | xor s, args => Some (keep s (List.fold_right Z.lxor 0 args))
    | slice lo sz, [a] => Some (keep sz (Z.shiftr a (Z.of_N lo)))
    | mul s, args => Some (keep s (List.fold_right Z.mul 1 args))
    | set_slice lo sz, [a; b] =>
        Some (Z.lor (Z.shiftl (keep sz b) (Z.of_N lo))
                    (Z.ldiff a (Z.shiftl (Z.ones (Z.of_N sz)) (Z.of_N lo))))
    | selectznz, [c; a; b] => Some (if Z.eqb c 0 then a else b)
    | iszero, [a] => Some (Z.b2z (Z.eqb a 0))
    | addZ, args => Some (List.fold_right Z.add 0 args)
    | mulZ, args => Some (List.fold_right Z.mul 1 args)
    | negZ, [a] => Some (Z.opp a)
    | shlZ, [a; b] => Some (Z.shiftl a b)
    | shrZ, [a; b] => Some (Z.shiftr a b)
    | andZ, args => Some (List.fold_right Z.land (-1) args)
    | orZ, args => Some (List.fold_right Z.lor 0 args)
    | xorZ, args => Some (List.fold_right Z.lxor 0 args)
    | addcarryZ s, args => Some (Z.shiftr (List.fold_right Z.add 0 args) (Z.of_N s))
    | subborrowZ s, cons a args' => Some (- Z.shiftr (a - List.fold_right Z.add 0 args') (Z.of_N s))
    | _, _ => None
    end%Z.
End WithContext.
Definition interp0_op := interp_op (fun _ => None).

Lemma interp_op_weaken_symbols G1 G2 o args
  (H : forall (s:symbol) v, G1 s = Some v -> G2 s = Some v)
  : forall v, interp_op G1 o args = Some v -> interp_op G2 o args = Some v.
Proof using Type.
  cbv [interp_op option_map]; intros;
    repeat (BreakMatch.break_match || BreakMatch.break_match_hyps);
    inversion_option; subst;
    try congruence.
  all : eapply H in Heqo0; congruence.
Qed.

Lemma interp_op_interp0_op o a v (H : interp0_op o a = Some v)
  : forall G, interp_op G o a = Some v.
Proof using Type. intros; eapply interp_op_weaken_symbols in H; try eassumption; discriminate. Qed.

Definition node_beq {A : Set} (arg_eqb : A -> A -> bool) : node A -> node A -> bool :=
  Prod.prod_beq _ _ op_beq (ListUtil.list_beq _ arg_eqb).
Global Instance reflect_node_beq {A : Set} {arg_eqb} {H : reflect_rel (@eq A) arg_eqb}
  : reflect_rel eq (@node_beq A arg_eqb) | 10 := _.

Class description := descr : option ((unit -> string) * bool (* always show *)).
Typeclasses Opaque description.
Definition eager_description := option (string * bool).
Notation Build_description descr always_show := (Some (fun 'tt => descr, always_show)) (only parsing).
Notation no_description := None (only parsing).

(* fresh symbols must have value <= their index, so that fresh symbols are truly fresh *)
Definition node_ok (i : idx) (n : node idx) := forall w s args, n = (old w s, args) -> (s <= i)%N.
Lemma new_node_ok n (pf : match n with (old _ _, _) => False | _ => True end) i : node_ok i n.
Proof. repeat intro; subst; assumption. Qed.
Existing Class node_ok.
Hint Extern 1 (node_ok ?i ?n) => exact (@new_node_ok n I i) : typeclass_instances.
Module Old.
Module dag.
  Definition t : Type := list (node idx * description).
  Definition empty : t := nil.
  Definition size (d : t) : N := N.of_nat (List.length d).
  Definition lookup (d : t) (i : idx) : option (node idx)
    := option_map fst (List.nth_error d (N.to_nat i)).
  Definition reverse_lookup (d : t) (i : node idx) : option idx
    := option_map N.of_nat (List.indexof (fun '(n', _) => node_beq N.eqb i n') d).
  Definition size_ok (d : t) : Prop
    := True.
  Definition all_nodes_ok (d : t) : Prop
    := forall i r, lookup d i = Some r -> node_ok i r.
  Definition ok (d : t) : Prop
  := size_ok d
     /\ (forall i n, reverse_lookup d n = Some i <-> lookup d i = Some n)
     /\ (forall i n, lookup d i = Some n -> (i < size d)%N).
  Definition merge_node {descr : description} (n : node idx) (d : t) : idx * t
    := match reverse_lookup d n with
       | Some i => (i, d)
       | None
         => (size d, d ++ [(n, descr)])
       end.
  Definition gensym (s:OperationSize) (d : t) : node idx
    := (old s (size d), []).
  Existing Class ok.
  Existing Class all_nodes_ok.

  Definition get_eager_description_description (d : eager_description) : option string
    := option_map fst d.
  Definition get_eager_description_always_show (d : eager_description) : bool
    := match d with Some (_, always_show) => always_show | None => false end.
  Definition force_description : description -> eager_description
    := option_map (fun '(descr, always_show) => (descr tt, always_show)).

  Module eager.
    Definition t := list (idx * node idx * eager_description).
    Definition force (d : dag.t) : eager.t
      := List.map (fun '(idx, (n, descr)) => (N.of_nat idx, n, force_description descr))
                  (List.enumerate d).
    Definition description_lookup (d : eager.t) (descr : string) : list idx
      := List.map (fun '(idx, _, _) => idx) (List.filter (fun '(_, _, descr') => match get_eager_description_description descr' with Some descr' => String.eqb descr descr' | _ => false end) d).
  End eager.

  Definition M T := t -> T * t.
  Definition bind {A B} (v : M A) (f : A -> M B) : M B
    := fun d => let '(v, d) := v d in f v d.
  Definition ret {A} (v : A) : M A
    := fun d => (v, d).

  Lemma iff_reverse_lookup_lookup d {ok : ok d}
    : forall i n, reverse_lookup d n = Some i <-> lookup d i = Some n.
  Proof. apply ok. Qed.

  Lemma lookup_value_size d {ok : ok d}
    : forall i n, lookup d i = Some n -> (i < size d)%N.
  Proof. apply ok. Qed.

  Lemma lookup_size_error d {ok : ok d}
    : forall i, (size d <= i)%N -> lookup d i = None.
  Proof.
    intro i; generalize (lookup_value_size d i); destruct lookup; intuition.
    specialize_under_binders_by reflexivity.
    lia.
  Qed.

  Lemma lookup_merge_node {descr : description} (n : node idx) (d : t) i
        {ok : ok d}
    : dag.lookup (snd (dag.merge_node n d)) i = match dag.lookup d i with
                                                | Some v => Some v
                                                | None
                                                  => if (i =? size d)%N && Option.is_None (reverse_lookup d n)
                                                     then Some n
                                                     else None
                                                end.
  Proof.
    cbv [dag.merge_node andb is_None lookup dag.ok size] in *;
      repeat first [ assumption
                   | reflexivity
                   | lia
                   | progress specialize_under_binders_by eassumption
                   | progress subst
                   | progress destruct_head'_and
                   | progress reflect_hyps
                   | progress cbn [fst snd option_map List.nth_error] in *
                   | progress cbv [option_map] in *
                   | rewrite Nat2N.id in *
                   | rewrite nth_error_app in *
                   | rewrite Nat.sub_diag in *
                   | rewrite nth_error_length_error in * by lia
                   | rewrite @nth_error_nil_error in *
                   | congruence
                   | break_innermost_match_step
                   | match goal with
                     | [ H : nth_error (_ :: _) ?x = _ |- _ ] => destruct x eqn:?; cbn [nth_error] in H
                     end ].
  Qed.

  Lemma reverse_lookup_merge_node {d : t}
        {ok : ok d} {descr : description} (n n' : node idx)
    : dag.reverse_lookup (snd (dag.merge_node n d)) n'
      = if node_beq N.eqb n' n
        then Some (fst (dag.merge_node n d))
        else dag.reverse_lookup d n'.
  Proof.
    cbv [dag.merge_node andb is_None reverse_lookup dag.ok size] in *;
      repeat first [ assumption
                   | reflexivity
                   | lia
                   | congruence
                   | progress inversion_option
                   | progress specialize_under_binders_by eassumption
                   | progress subst
                   | progress destruct_head'_and
                   | progress reflect_hyps
                   | rewrite @indexof_app in *
                   | progress cbv [option_map Option.value Option.sequence idx] in *
                   | progress cbn [fst snd option_map indexof] in *
                   | rewrite Nat.add_0_r
                   | congruence
                   | break_innermost_match_step
                   | progress break_match
                   | progress break_match_hyps ].
  Qed.

  Lemma fst_merge_node {descr : description} (n : node idx) (d : t)
    : fst (dag.merge_node n d) = match reverse_lookup d n with
                                 | Some i => i
                                 | None => size d
                                 end.
  Proof. cbv [merge_node]; break_innermost_match; reflexivity. Qed.

  Lemma reverse_lookup_gensym s (d : t)
        {ok : ok d}
        {all_nodes_ok : all_nodes_ok d}
    : dag.reverse_lookup d (gensym s d) = None.
  Proof.
    cbv [dag.all_nodes_ok] in *.
    destruct (reverse_lookup d (gensym s d)) as [i|] eqn:H; [ | reflexivity ].
    rewrite iff_reverse_lookup_lookup in H by assumption.
    cbv [node_ok gensym] in *.
    specialize_under_binders_by eassumption.
    specialize_under_binders_by reflexivity.
    apply lookup_value_size in H; trivial.
    lia.
  Qed.

  Lemma lookup_merge_node_gensym {descr : description} s (d : t) i
        {ok : ok d}
        {all_nodes_ok : all_nodes_ok d}
    : dag.lookup (snd (dag.merge_node (gensym s d) d)) i
      = if (i =? size d)%N
        then Some (gensym s d)
        else dag.lookup d i.
  Proof.
    rewrite lookup_merge_node, reverse_lookup_gensym by assumption.
    cbv [andb is_None].
    break_innermost_match; try reflexivity; reflect_hyps; subst.
    rewrite lookup_size_error in * by first [ assumption | lia ].
    congruence.
  Qed.

  Lemma fst_merge_node_gensym {descr : description} s (d : t)
        {ok : ok d}
        {all_nodes_ok : all_nodes_ok d}
    : fst (dag.merge_node (gensym s d) d) = size d.
  Proof.
    rewrite fst_merge_node, reverse_lookup_gensym by assumption; reflexivity.
  Qed.

  Lemma lookup_empty i : lookup empty i = None.
  Proof. cbv [empty lookup]; now rewrite nth_error_nil_error. Qed.
  Lemma reverse_lookup_empty n : reverse_lookup empty n = None.
  Proof. reflexivity. Qed.
  Lemma size_empty : size empty = 0%N.
  Proof. reflexivity. Qed.

  Lemma size_merge_node {descr:description} n (d:t)
    : size (snd (merge_node n d)) = match reverse_lookup d n with Some _ => size d | None => N.succ (size d) end.
  Proof.
    cbv [merge_node size]; break_innermost_match; cbn [snd] in *; inversion_pair; subst; rewrite ?app_length; cbn [List.length]; lia.
  Qed.

  Lemma size_merge_node_le {descr:description} n (d:t)
    : (size d <= size (snd (merge_node n d)))%N.
  Proof.
    rewrite size_merge_node; break_innermost_match; lia.
  Qed.

  Lemma size_merge_node_gensym {descr:description} s (d:t)
        {ok : ok d}
        {all_nodes_ok : all_nodes_ok d}
    : size (snd (merge_node (gensym s d) d)) = N.succ (size d).
  Proof. rewrite size_merge_node, reverse_lookup_gensym by assumption; reflexivity. Qed.

  Global Instance empty_ok : ok empty | 10.
  Proof.
    repeat apply conj; cbv [size empty]; intros *; cbv [lookup];
      rewrite ?nth_error_nil_error; cbn; try exact I;
      intuition first [ congruence | lia ].
  Qed.
  Global Instance empty_all_nodes_ok : all_nodes_ok empty | 10.
  Proof.
    repeat intro; subst; rewrite lookup_empty in *; congruence.
  Qed.
  Global Instance merge_node_ok {descr:description} {n:node idx} {d : t} {dok : ok d} : ok (snd (merge_node n d)) | 10.
  Proof.
    repeat apply conj; cbv [size empty size_ok]; intros *.
    all: rewrite ?lookup_merge_node, ?reverse_lookup_merge_node by assumption.
    all: let tac :=
           repeat first [ progress cbv [ok size_ok size merge_node lookup reverse_lookup] in *
                        | progress destruct_head'_and
                        | progress inversion_option
                        | progress subst
                        | exfalso; assumption
                        | progress inversion_pair
                        | progress cbn [fst snd List.length] in *
                        | break_innermost_match_step
                        | progress intros
                        | progress destruct_head'_ex
                        | progress destruct_head'_and
                        | progress reflect_hyps
                        | progress split_iff
                        | apply conj
                        | exact I
                        | progress cbv [option_map idx] in *
                        | progress break_match
                        | progress break_match_hyps
                        | lia
                        | congruence
                        | rewrite Nat2N.id in *
                        | rewrite N2Nat.id in *
                        | rewrite app_length
                        | progress specialize_under_binders_by reflexivity
                        | progress specialize_under_binders_by rewrite Nat2N.id
                        | progress destruct_head'_prod
                        | match goal with
                          | [ H : forall i n, match nth_error _ (N.to_nat i) with _ => _ end = _ -> _ |- _ ]
                            => specialize (fun i => H (N.of_nat i))
                          | [ H : _ = Some _ |- _ ] => rewrite H in *
                          | [ H : N.of_nat _ = N.of_nat _ |- _ ] => apply (f_equal N.to_nat) in H
                          end
                        | solve [ exfalso; auto ] ] in
         tac;
         repeat match goal with
                | [ H : _ = Some _ |- _ ] => progress specialize_all_ways_under_binders_by rewrite H
                end;
         tac.
  Qed.
  Global Instance merge_node_all_nodes_ok {descr:description} {n:node idx} {d : t} {dok : ok d} {dnok : all_nodes_ok d} {nok : node_ok (size d) n}
    : all_nodes_ok (snd (merge_node n d)) | 10.
  Proof.
    cbv [all_nodes_ok] in *; intros i r; specialize (dnok i r).
    rewrite lookup_merge_node in * by assumption.
    cbv [andb is_None]; break_innermost_match; intros; inversion_option; reflect_hyps; subst; auto.
  Qed.
  Global Instance gensym_node_ok s d : node_ok (size d) (gensym s d) | 10.
  Proof.
    cbv [node_ok]; intros * H.
    inversion H; subst; reflexivity.
  Qed.
  Global Hint Extern 1 (node_ok (size _) (gensym _ _)) => exact (@gensym_node_ok _ _) : typeclass_instances.

  Lemma eq_fst_merge_node_change_descr {descr1 descr2 : description} (n : node idx) (d : t)
    : fst (@merge_node descr1 n d) = fst (@merge_node descr2 n d).
  Proof.
    cbv [merge_node]; break_innermost_match; reflexivity.
  Qed.

  (* lemmas below here don't unfold the definitions *)
  Lemma lookup_merge_node' {descr1 descr2 : description} (n : node idx) (d : t)
        {ok : ok d}
    : dag.lookup (snd (@dag.merge_node descr1 n d)) (fst (@dag.merge_node descr2 n d)) = Some n.
  Proof.
    rewrite lookup_merge_node, fst_merge_node by assumption.
    cbv [andb is_None].
    repeat first [ rewrite iff_reverse_lookup_lookup in * by assumption
                 | rewrite lookup_size_error in * by first [ assumption | lia ]
                 | progress inversion_option
                 | progress subst
                 | reflexivity
                 | progress reflect_hyps
                 | lia
                 | break_innermost_match_step ].
  Qed.
End dag.
End Old.
Module New.
Module dag.
  Module IdxMap <: UsualS := NMap <+ FMapFacts.Facts <+ Facts_RemoveHints <+ FMapFacts.AdditionalFacts.
  Module ListIdxMap <: UsualS := ListNMap.
  Module NodeIdxMap <: UsualS := ProdUsualMap OpMap ListIdxMap <+ FMapFacts.Facts <+ Facts_RemoveHints <+ FMapFacts.AdditionalFacts.
  Module IdxMapProperties := FMapFacts.OrdProperties IdxMap <+ OrdProperties_RemoveHints IdxMap.
  Module NodeIdxMapProperties := FMapFacts.OrdProperties NodeIdxMap <+ OrdProperties_RemoveHints NodeIdxMap.

  Definition t : Type := NodeIdxMap.t idx * IdxMap.t (node idx * description) * N (* size *).
  Definition empty : t := (@NodeIdxMap.empty _, @IdxMap.empty _, 0%N).
  Definition size (d : t) : N := let '(_, _, sz) := d in sz.
  Definition lookup (d : t) (i : idx) : option (node idx)
    := let '(_, d, _) := d in option_map (@fst _ _) (IdxMap.find i d).
  Definition reverse_lookup (d : t) (i : node idx) : option idx
    := let '(d, _, _) := d in NodeIdxMap.find i d.
  Definition size_ok (d : t) : Prop
    := let '(im, nm, n) := d in
       NodeIdxMap.cardinal im = N.to_nat (size d)
       /\ IdxMap.cardinal nm = N.to_nat (size d).
  Definition all_nodes_ok (d : t) : Prop
    := forall i r, lookup d i = Some r -> node_ok i r.
  Definition ok (d : t) : Prop
  := size_ok d
     /\ (forall i n, reverse_lookup d n = Some i <-> lookup d i = Some n)
     /\ (forall i n, lookup d i = Some n -> (i < size d)%N).
  Definition merge_node {descr : description} (n : node idx) (d : t) : idx * t
    := match reverse_lookup d n with
       | Some i => (i, d)
       | None
         => let '(d, d', sz) := d in
            (sz, (NodeIdxMap.add n sz d, IdxMap.add sz (n, descr) d', N.succ sz))
       end.
  Definition gensym (s:OperationSize) (d : t) : node idx
    := (old s (size d), []).
  Existing Class ok.
  Existing Class all_nodes_ok.

  Definition get_eager_description_description (d : eager_description) : option string
    := option_map fst d.
  Definition get_eager_description_always_show (d : eager_description) : bool
    := match d with Some (_, always_show) => always_show | None => false end.
  Definition force_description : description -> eager_description
    := option_map (fun '(descr, always_show) => (descr tt, always_show)).

  Module eager.
    Definition t := list (idx * node idx * eager_description).
    Definition force (d : dag.t) : eager.t
      := List.map (fun '(idx, (n, descr)) => (idx, n, force_description descr))
                  (IdxMap.elements (let '(_, d, _) := d in d)).
    Definition description_lookup (d : eager.t) (descr : string) : list idx
      := List.map (fun '(idx, _, _) => idx) (List.filter (fun '(_, _, descr') => match get_eager_description_description descr' with Some descr' => String.eqb descr descr' | _ => false end) d).
  End eager.

  Definition M T := t -> T * t.
  Definition bind {A B} (v : M A) (f : A -> M B) : M B
    := fun d => let '(v, d) := v d in f v d.
  Definition ret {A} (v : A) : M A
    := fun d => (v, d).

  Lemma iff_reverse_lookup_lookup d {ok : ok d}
    : forall i n, reverse_lookup d n = Some i <-> lookup d i = Some n.
  Proof. apply ok. Qed.

  Lemma lookup_value_size d {ok : ok d}
    : forall i n, lookup d i = Some n -> (i < size d)%N.
  Proof. apply ok. Qed.

  Lemma lookup_size_error d {ok : ok d}
    : forall i, (size d <= i)%N -> lookup d i = None.
  Proof.
    intro i; generalize (lookup_value_size d i); destruct lookup; intuition.
    specialize_under_binders_by reflexivity.
    lia.
  Qed.

  Lemma lookup_merge_node {descr : description} (n : node idx) (d : t) i
        {ok : ok d}
    : dag.lookup (snd (dag.merge_node n d)) i = match dag.lookup d i with
                                                | Some v => Some v
                                                | None
                                                  => if (i =? size d)%N && Option.is_None (reverse_lookup d n)
                                                     then Some n
                                                     else None
                                                end.
  Proof.
    cbv [dag.merge_node andb is_None lookup dag.ok size] in *;
      repeat first [ assumption
                   | reflexivity
                   | lia
                   | progress specialize_under_binders_by eassumption
                   | progress subst
                   | progress destruct_head'_and
                   | progress reflect_hyps
                   | progress cbn [fst snd option_map] in *
                   | rewrite IdxMap.add_o
                   | break_innermost_match_step ].
  Qed.

  Lemma reverse_lookup_merge_node {d : t}
        {ok : ok d} {descr : description} (n n' : node idx)
    : dag.reverse_lookup (snd (dag.merge_node n d)) n'
      = if node_beq N.eqb n' n
        then Some (fst (dag.merge_node n d))
        else dag.reverse_lookup d n'.
  Proof.
    cbv [dag.merge_node andb is_None reverse_lookup dag.ok size] in *;
      repeat first [ assumption
                   | reflexivity
                   | lia
                   | congruence
                   | progress specialize_under_binders_by eassumption
                   | progress subst
                   | progress destruct_head'_and
                   | progress reflect_hyps
                   | progress cbn [fst snd option_map] in *
                   | rewrite NodeIdxMap.add_o
                   | break_innermost_match_step ].
  Qed.

  Lemma fst_merge_node {descr : description} (n : node idx) (d : t)
    : fst (dag.merge_node n d) = match reverse_lookup d n with
                                 | Some i => i
                                 | None => size d
                                 end.
  Proof. cbv [merge_node]; break_innermost_match; reflexivity. Qed.

  Lemma reverse_lookup_gensym s (d : t)
        {ok : ok d}
        {all_nodes_ok : all_nodes_ok d}
    : dag.reverse_lookup d (gensym s d) = None.
  Proof.
    cbv [dag.all_nodes_ok] in *.
    destruct (reverse_lookup d (gensym s d)) as [i|] eqn:H; [ | reflexivity ].
    rewrite iff_reverse_lookup_lookup in H by assumption.
    cbv [node_ok gensym] in *.
    specialize_under_binders_by eassumption.
    specialize_under_binders_by reflexivity.
    apply lookup_value_size in H; trivial.
    lia.
  Qed.

  Lemma lookup_merge_node_gensym {descr : description} s (d : t) i
        {ok : ok d}
        {all_nodes_ok : all_nodes_ok d}
    : dag.lookup (snd (dag.merge_node (gensym s d) d)) i
      = if (i =? size d)%N
        then Some (gensym s d)
        else dag.lookup d i.
  Proof.
    rewrite lookup_merge_node, reverse_lookup_gensym by assumption.
    cbv [andb is_None].
    break_innermost_match; try reflexivity; reflect_hyps; subst.
    rewrite lookup_size_error in * by first [ assumption | lia ].
    congruence.
    Qed.

  Lemma fst_merge_node_gensym {descr : description} s (d : t)
        {ok : ok d}
        {all_nodes_ok : all_nodes_ok d}
    : fst (dag.merge_node (gensym s d) d) = size d.
  Proof.
    rewrite fst_merge_node, reverse_lookup_gensym by assumption; reflexivity.
  Qed.

  Lemma lookup_empty i : lookup empty i = None.
  Proof. cbv [empty lookup]; now rewrite IdxMap.find_empty. Qed.
  Lemma reverse_lookup_empty n : reverse_lookup empty n = None.
  Proof. cbv [empty reverse_lookup]; now rewrite NodeIdxMap.find_empty. Qed.
  Lemma size_empty : size empty = 0%N.
  Proof. reflexivity. Qed.

  Lemma size_merge_node {descr:description} n (d:t)
    : size (snd (merge_node n d)) = match reverse_lookup d n with Some _ => size d | None => N.succ (size d) end.
  Proof.
    cbv [merge_node size]; break_innermost_match; cbn [snd] in *; inversion_pair; subst; try reflexivity.
  Qed.

  Lemma size_merge_node_le {descr:description} n (d:t)
    : (size d <= size (snd (merge_node n d)))%N.
  Proof.
    rewrite size_merge_node; break_innermost_match; lia.
  Qed.

  Lemma size_merge_node_gensym {descr:description} s (d:t)
        {ok : ok d}
        {all_nodes_ok : all_nodes_ok d}
    : size (snd (merge_node (gensym s d) d)) = N.succ (size d).
  Proof. rewrite size_merge_node, reverse_lookup_gensym by assumption; reflexivity. Qed.

  Global Instance empty_ok : ok empty | 10.
  Proof.
    repeat apply conj; cbv [size empty].
    { apply NodeIdxMapProperties.P.cardinal_1, NodeIdxMap.empty_1. }
    { apply IdxMapProperties.P.cardinal_1, IdxMap.empty_1. }
    all: cbv [lookup reverse_lookup]; intros *.
    all: rewrite ?NodeIdxMap.empty_o, ?IdxMap.empty_o; cbn; intuition congruence.
  Qed.
  Global Instance empty_all_nodes_ok : all_nodes_ok empty | 10.
  Proof.
    repeat intro; subst; rewrite lookup_empty in *; congruence.
  Qed.
  Global Instance merge_node_ok {descr:description} {n:node idx} {d : t} {dok : ok d} : ok (snd (merge_node n d)) | 10.
  Proof.
    repeat apply conj; cbv [size empty size_ok]; intros *.
    all: rewrite ?lookup_merge_node, ?reverse_lookup_merge_node by assumption.
    all: repeat first [ progress cbv [ok size_ok size merge_node lookup reverse_lookup] in *
                      | progress destruct_head'_and
                      | progress inversion_option
                      | progress subst
                      | exfalso; assumption
                      | progress inversion_pair
                      | progress cbn [fst snd] in *
                      | break_innermost_match_step
                      | progress intros
                      | progress reflect_hyps
                      | progress split_iff
                      | apply conj
                      | rewrite NodeIdxMap.cardinal_add, NodeIdxMap.mem_find_b
                      | rewrite IdxMap.cardinal_add, IdxMap.mem_find_b
                      | rewrite N2Nat.inj_succ
                      | lia
                      | congruence
                      | solve [ auto ]
                      | match goal with
                        | [ H : ?x = Some _ |- _ ] => rewrite H in *
                        end
                      | progress specialize_under_binders_by reflexivity
                      | match goal with
                        | [ H : _ |- _ ] => progress specialize_all_ways_under_binders_by exact H
                        | [ H : _ |- _ ] => progress specialize_all_ways_under_binders_by rewrite H
                        end ].
  Qed.
  Global Instance merge_node_all_nodes_ok {descr:description} {n:node idx} {d : t} {dok : ok d} {dnok : all_nodes_ok d} {nok : node_ok (size d) n}
    : all_nodes_ok (snd (merge_node n d)) | 10.
  Proof.
    cbv [all_nodes_ok] in *; intros i r; specialize (dnok i r).
    rewrite lookup_merge_node in * by assumption.
    cbv [andb is_None]; break_innermost_match; intros; inversion_option; reflect_hyps; subst; auto.
  Qed.
  Global Instance gensym_node_ok s d : node_ok (size d) (gensym s d) | 10.
  Proof.
    cbv [node_ok]; intros * H.
    inversion H; subst; reflexivity.
  Qed.
  Global Hint Extern 1 (node_ok (size _) (gensym _ _)) => exact (@gensym_node_ok _ _) : typeclass_instances.

  Lemma eq_fst_merge_node_change_descr {descr1 descr2 : description} (n : node idx) (d : t)
    : fst (@merge_node descr1 n d) = fst (@merge_node descr2 n d).
  Proof.
    cbv [merge_node]; break_innermost_match; reflexivity.
  Qed.

  (* lemmas below here don't unfold the definitions *)
  Lemma lookup_merge_node' {descr1 descr2 : description} (n : node idx) (d : t)
        {ok : ok d}
    : dag.lookup (snd (@dag.merge_node descr1 n d)) (fst (@dag.merge_node descr2 n d)) = Some n.
  Proof.
    rewrite lookup_merge_node, fst_merge_node by assumption.
    cbv [andb is_None].
    repeat first [ rewrite iff_reverse_lookup_lookup in * by assumption
                 | rewrite lookup_size_error in * by first [ assumption | lia ]
                 | progress inversion_option
                 | progress subst
                 | reflexivity
                 | progress reflect_hyps
                 | lia
                 | break_innermost_match_step ].
  Qed.
End dag.
End New.
Export Old.
Global Arguments dag.t : simpl never.
Global Arguments dag.empty : simpl never.
Global Arguments dag.size : simpl never.
Global Arguments dag.lookup : simpl never.
Global Arguments dag.reverse_lookup : simpl never.
Global Arguments dag.ok : simpl never.
Global Arguments dag.all_nodes_ok : simpl never.
Global Arguments dag.merge_node : simpl never.
Global Arguments dag.gensym : simpl never.
Global Strategy 1000 [
      dag.t
        dag.empty
        dag.size
        dag.lookup
        dag.reverse_lookup
        dag.ok
        dag.all_nodes_ok
        dag.merge_node
        dag.gensym
    ].
Notation dag := dag.t.
Delimit Scope dagM_scope with dagM.
Bind Scope dagM_scope with dag.M.
Notation "x <- y ; f" := (dag.bind y (fun x => f%dagM)) : dagM_scope.

Section WithDag.
  Context (ctx : symbol -> option Z) (dag : dag.t).
  Definition reveal_step reveal (i : idx) : expr :=
    match dag.lookup dag i with
    | None => (* undefined *) ExprRef i
    | Some (op, args) => ExprApp (op, List.map reveal args)
    end.
  Fixpoint reveal (n : nat) (i : idx) :=
    match n with
    | O => ExprRef i
    | S n => reveal_step (reveal n) i
    end.

  Print op.

  Definition f :=
    let (a, b) := (7, 6) in a + b.

  Print List.map.


  Definition reveal_node n '(op, args) :=
    ExprApp (op, List.map (reveal n) args).

  (** given a set of indices, get the set of indices of their arguments *)
  Definition reveal_gather_deps_args (ls : NSet.t) : NSet.t
    := fold_right
         (fun i so_far => match dag.lookup dag i with
                          | None => so_far
                          | Some (_op, args) => fold_right NSet.add so_far args
                          end)
         NSet.empty
         (NSet.elements ls).

  (** given a set of seen indices and a set of newly-revealed indices,
  we want to merge the new indices into what's been seen and recurse
  on the new indices *)
  Definition reveal_gather_deps_step reveal_gather_deps (so_far : NSet.t) (new_idxs : NSet.t) : NSet.t
    := let new_idxs := NSet.diff new_idxs so_far in
       if NSet.is_empty new_idxs
       then so_far
       else reveal_gather_deps (NSet.union so_far new_idxs) (reveal_gather_deps_args new_idxs).

  Fixpoint reveal_gather_deps_list (n : nat) (so_far : NSet.t) (new_idxs : NSet.t) : NSet.t
    := match n with
       | O => NSet.union so_far new_idxs
       | S n => reveal_gather_deps_step (reveal_gather_deps_list n) so_far new_idxs
       end.

  Definition reveal_gather_deps (n : nat) (i : idx) : NSet.t
    := reveal_gather_deps_list n NSet.empty (NSet.singleton i).

  Definition reveal_step_from_deps reveal (deps : NSet.t) (i : idx) : expr
    := if NSet.mem i deps
       then match dag.lookup dag i with
            | None => (* undefined *) ExprRef i
            | Some (op, args) => ExprApp (op, List.map reveal args)
            end
       else ExprRef i.
  Fixpoint reveal_from_deps_fueled (fuel : nat) (deps : NSet.t) (i : idx) :=
    match fuel with
    | O => ExprRef i
    | S fuel => reveal_step_from_deps (reveal_from_deps_fueled fuel deps) deps i
    end.
  (** depth determines which indices get expanded, but all references
  to the same index get expanded if they appear in the output *)
  Definition reveal_at_least n (i : idx) : expr
    := reveal_from_deps_fueled (S (N.to_nat (dag.size dag))) (reveal_gather_deps n i) i.

  Definition reveal_node_at_least n '(op, args) :=
    ExprApp (op, List.map (reveal_at_least n) args).

  Local Unset Elimination Schemes.
  Inductive eval : expr -> Z -> Prop :=
  | ERef i op args args' n
    (_:dag.lookup dag i = Some (op, args))
    (_:List.Forall2 eval (map ExprRef args) args')
    (_:interp_op ctx op args' = Some n)
    : eval (ExprRef i) n
  | EApp op args args' n
    (_:List.Forall2 eval args args')
    (_:interp_op ctx op args' = Some n)
    : eval (ExprApp (op, args)) n.

  Variant eval_node : node idx -> Z -> Prop :=
  | ENod op args args' n
    (_:List.Forall2 eval (map ExprRef args) args')
    (_:interp_op ctx op args' = Some n)
    : eval_node (op, args) n.


  Section eval_ind.
    Context (P : expr -> Z -> Prop)
      (HRef : forall i op args args' n, dag.lookup dag i = Some (op, args) ->
        Forall2 (fun e n => eval e n /\ P e n) (map ExprRef args) args' ->
        interp_op ctx op args' = Some n ->
        P (ExprRef i) n)
      (HApp : forall op args args' n,
        Forall2 (fun i e => eval i e /\ P i e) args args' ->
        interp_op ctx op args' = Some n ->
        P (ExprApp (op, args)) n).
    Fixpoint eval_ind i n (pf : eval i n) {struct pf} : P i n :=
      match pf with
      | ERef _ _ _ _ _ A B C => HRef _ _ _ _ _ A (Forall2_weaken (fun _ _ D => conj D (eval_ind _ _ D)) _ _ B) C
      | EApp _ _ _ _ A B => HApp _ _ _ _ (Forall2_weaken (fun _ _ C => conj C (eval_ind _ _ C)) _ _ A) B
      end.
  End eval_ind.

  Lemma eval_eval : forall e v1, eval e v1 -> forall v2, eval e v2 -> v1=v2.
  Proof using Type.
    induction 1; inversion 1; subst;
    enough (args' = args'0) by congruence;
    try replace args0 with args in * by congruence.
    { eapply Forall2_map_l in H0.
      eapply Forall2_flip in H0.
      eapply (proj1 (Forall2_map_l _ _ _)) in H5.
      epose proof Forall2_trans H0 H5 as HH.
      eapply Forall2_eq, Forall2_weaken, HH; cbv beta; clear; firstorder. }
    { eapply Forall2_flip in H.
      epose proof Forall2_trans H H4 as HH.
      eapply Forall2_eq, Forall2_weaken, HH; cbv beta; clear; firstorder. }
  Qed.

  Lemma eval_eval_Forall2 xs vxs (_ : Forall2 eval xs vxs)
    vys (_ : Forall2 eval xs vys) : vxs = vys.
  Proof using Type.
    revert dependent vys; induction H; inversion 1; subst;
      eauto; eauto using f_equal2, IHForall2, eval_eval.
  Qed.

  Lemma eval_reveal : forall n i, forall v, eval (ExprRef i) v ->
    forall e, reveal n i = e -> eval e v.
  Proof using Type.
    induction n; cbn [reveal]; cbv [reveal_step]; intros; subst; eauto; [].
    inversion H; subst; clear H.
    rewrite H1; econstructor; try eassumption; [].
    eapply (proj1 (Forall2_map_l _ _ _)) in H2.
    clear dependent i; clear dependent v.
    induction H2; cbn; eauto.
  Qed.

  Lemma eval_node_reveal_node : forall n v, eval_node n v ->
    forall f e, reveal_node f n = e -> eval e v.
  Proof using Type.
    cbv [reveal_node]; inversion 1; intros; subst.
    econstructor; eauto.
    eapply (proj1 (Forall2_map_l _ _ _)) in H0; eapply Forall2_map_l.
    eapply Forall2_weaken; try eassumption; []; cbv beta; intros.
    eapply eval_reveal; eauto.
  Qed.

  Lemma eval_reveal_from_deps_fueled deps : forall n i, forall v, eval (ExprRef i) v ->
    forall e, reveal_from_deps_fueled n deps i = e -> eval e v.
  Proof using Type.
    induction n; cbn [reveal_from_deps_fueled]; cbv [reveal_step_from_deps]; intros; subst; eauto; [].
    break_innermost_match_step; eauto; [].
    inversion H; subst; clear H.
    rewrite H1; econstructor; try eassumption; [].
    eapply (proj1 (Forall2_map_l _ _ _)) in H2.
    clear dependent i; clear dependent v.
    induction H2; cbn; eauto.
  Qed.

  Lemma eval_reveal_at_least : forall n i, forall v, eval (ExprRef i) v ->
    forall e, reveal_at_least n i = e -> eval e v.
  Proof using Type.
    cbv [reveal_at_least].
    intros; eapply eval_reveal_from_deps_fueled; eassumption.
  Qed.

  Lemma eval_node_reveal_node_at_least : forall n v, eval_node n v ->
    forall f e, reveal_node_at_least f n = e -> eval e v.
  Proof using Type.
    cbv [reveal_node]; inversion 1; intros; subst.
    econstructor; eauto.
    eapply (proj1 (Forall2_map_l _ _ _)) in H0; eapply Forall2_map_l.
    eapply Forall2_weaken; try eassumption; []; cbv beta; intros.
    eapply eval_reveal_at_least; eauto.
  Qed.
End WithDag.

Definition merge_node {descr : description} (n : node idx) : dag.M idx
  := dag.merge_node n.

Print partition.

Print op.
Print OperationSize.

Definition is_adc_expr (s : OperationSize) (e : expr) : bool :=
  match e with
  | ExprRef _ => false
  | ExprApp (o, args) => op_beq (addcarry s) o
  end.

Print fold_right.
Print map.
Locate "++".

Print reveal.
Print reveal_step.
Print dag.lookup.

Print N. Print positive.

Local Open Scope Z_scope.

Fixpoint bound_expr e : option Z := (* e <= r *)
  match e with
  | ExprApp (const v, _) => if Z.leb 0 v then Some v else None
  | ExprApp (add s, args) =>
      Some  match Option.List.lift (List.map bound_expr args) with
            | Some bounds => Z.min (List.fold_right Z.add 0%Z bounds) (Z.ones (Z.of_N s))
            | None => Z.ones (Z.of_N s)
            end
  | ExprApp (selectznz, [c;a;b]) =>
      match bound_expr a, bound_expr b with
      | Some a, Some b => Some (Z.max a b)
      | _, _ => None
      end
  | ExprApp (set_slice 0 w, [a;b]) =>
      match bound_expr a, bound_expr b with
      | Some a, Some b => Some (Z.lor
                                  (Z.land (Z.ones (Z.succ (Z.log2 b))) (Z.ones (Z.of_N w)))
                                  (Z.ldiff (Z.ones (Z.succ (Z.log2 a))) (Z.ones (Z.of_N w))))
      | _, _ => None
      end
  | ExprApp ((old s _ | slice _ s | mul s | shl s | shr s | sar s | neg s | and s | or s | xor s), _) => Some (Z.ones (Z.of_N s))
  | ExprApp ((addcarry _ | subborrow _ | addoverflow _ | iszero), _) => Some 1
  | _ => None
  end%Z.

Definition is_bounded_by (d : dag) (m : Z) (i : idx) : bool :=
  match bound_expr (reveal d 1 i) with (* we only reveal one layer here.  That could be changed. *)
  | None => false
  | Some b => b <=? m
  end.

Print andb.
Check fold_right.

(* range of addends does not matter. *)
Fixpoint list_of_addends (d : dag) (f : nat) (s : OperationSize) (i : idx) : list idx :=
  match f with
  | S f' =>
    match dag.lookup d i with
    | Some (o, args) =>
        match o with
        | add s' => if N.leb s s' then fold_right (@app idx) [] (map (list_of_addends d f' s) args) else [i]
        | addZ => fold_right (@app idx) [] (map (list_of_addends d f' s) args)
        | _ => [i]
        end
    | None => [i]
    end
  | O => [i]
  end.

Local Open Scope Z_scope.

Lemma Z_land_ones' : forall (s : N) (a : Z), Z.land a (Z.ones (Z.of_N s)) = (a mod 2 ^ Z.of_N s)%Z.
Proof. intros. assert (E: Z.le 0 (Z.of_N s)) by lia. auto using Z.land_ones. Qed.

Lemma break_addZ_small : forall l1 l2,
  (fold_right Z.add 0 l1) + (fold_right Z.add 0 l2) = fold_right Z.add 0 (l1 ++ l2).
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. rewrite <- IHl1. lia.
Qed.

Lemma break_add (m1 m2 n : Z) ctx d s l1 l2:
  interp_op (fun _ => None) (add s) [m1; m2] = Some n ->
  eval ctx d (ExprApp (add s, l1)) m1 ->
  eval ctx d (ExprApp (add s, l2)) m2 ->
  eval ctx d (ExprApp (add s, l1 ++ l2)) n.
Proof.
  simpl. intros. inversion H0; subst. inversion H1; subst.
  apply (EApp _ _ _ _ (args' ++ args'0)).
  - apply Forall2_app.
    + apply H4.
    + apply H5.
  - simpl. f_equal. injection H as H. rewrite <- H. injection H6 as H6. injection H8 as H8.
    rewrite <- H6. rewrite <- H8. rewrite Z.add_0_r. repeat rewrite Z_land_ones'. rewrite <- break_addZ_small.
    rewrite <- PullPush.Z.add_mod_full. reflexivity.
Qed.

Lemma break_addZ (m1 m2 n : Z) ctx d l1 l2:
  interp_op (fun _ => None) addZ [m1; m2] = Some n ->
  eval ctx d (ExprApp (addZ, l1)) m1 ->
  eval ctx d (ExprApp (addZ, l2)) m2 ->
  eval ctx d (ExprApp (addZ, l1 ++ l2)) n.
Proof.
  simpl. intros. inversion H0; subst. inversion H1; subst.
  apply (EApp _ _ _ _ (args' ++ args'0)).
  - apply Forall2_app.
    + apply H4.
    + apply H5.
  - simpl. f_equal. injection H as H. rewrite <- H. injection H6 as H6. injection H8 as H8.
    rewrite <- H6. rewrite <- H8. symmetry. rewrite Z.add_0_r. apply break_addZ_small.
Qed.

Lemma break_add_backwards (n : Z) ctx d s l1 l2:
  eval ctx d (ExprApp (add s, l1 ++ l2)) n ->
  exists m1 m2,
  interp_op (fun _ => None) (add s) [m1; m2] = Some n /\
  eval ctx d (ExprApp (add s, l1)) m1 /\
  eval ctx d (ExprApp (add s, l2)) m2.
Proof.
  intros. Check interp_op. inversion H; subst. Search Forall2. apply Forall2_app_inv_l in H2.
  destruct H2 as [l1' [l2' [H1 [H2 H3] ] ] ]. Check interp_op.
  assert (E1: exists m1, interp_op ctx (add s) l1' = Some m1). { simpl. eauto. }
  assert (E2: exists m2, interp_op ctx (add s) l2' = Some m2). { simpl. eauto. }
  destruct E1 as [m1 E1]. destruct E2 as [m2 E2].
  exists m1. exists m2. split.
  - simpl. f_equal. rewrite Z.add_0_r. simpl in H4. injection H4 as H4. simpl in E1. simpl in E2. subst.
    injection E1 as E1. injection E2 as E2. subst. repeat rewrite Z_land_ones'. rewrite <- break_addZ_small.
    rewrite <- PullPush.Z.add_mod_full. reflexivity.
  - split.
    + apply EApp with (args' := l1'); assumption.
    + apply EApp with (args' := l2'); assumption.
Qed.

Lemma break_addZ_backwards (n : Z) ctx d l1 l2:
  eval ctx d (ExprApp (addZ, l1 ++ l2)) n ->
  exists m1 m2,
  interp_op (fun _ => None) addZ [m1; m2] = Some n /\
  eval ctx d (ExprApp (addZ, l1)) m1 /\
  eval ctx d (ExprApp (addZ, l2)) m2.
Proof.
  intros. Check interp_op. inversion H; subst. Search Forall2. apply Forall2_app_inv_l in H2.
  destruct H2 as [l1' [l2' [H1 [H2 H3] ] ] ]. Check interp_op.
  assert (E1: exists m1, interp_op ctx (addZ) l1' = Some m1). { simpl. eauto. }
  assert (E2: exists m2, interp_op ctx (addZ) l2' = Some m2). { simpl. eauto. }
  destruct E1 as [m1 E1]. destruct E2 as [m2 E2].
  exists m1. exists m2. split.
  - simpl. f_equal. rewrite Z.add_0_r. simpl in H4. injection H4 as H4. simpl in E1. simpl in E2. subst.
    injection E1 as E1. injection E2 as E2. subst. rewrite <- break_addZ_small. reflexivity.
  - split.
    + apply EApp with (args' := l1'); assumption.
    + apply EApp with (args' := l2'); assumption.
Qed.

Lemma app_is_cons {X} (x : X) (l : list X):
  x :: l = [x] ++ l.
Proof. reflexivity. Qed.

Compute (Z.land 0 (-100)).

Lemma and_pos : forall x y,
  Z.le 0 y -> Z.le 0 (Z.land x y).
Proof.
  intros. cbv [Z.land]. destruct x as [| a| a]; destruct y as [| b| b]; lia.
Qed.

Check Z.land_ones.
Print Z.mod_small.
Compute (-1 mod 5)%Z.
Lemma le_and_ones y n: 
  Z.le 0 y /\ Z.le y (Z.ones (Z.of_N n)) -> Z.land y (Z.ones (Z.of_N n)) = y.
Proof.
  intros. assert (E: Z.le 0 (Z.of_N n)) by lia. apply (Z.land_ones y) in E.
  rewrite E. clear E. apply Z.mod_small. cbv [Z.ones] in H. rewrite Z.shiftl_1_l in H.
  lia.
Qed.

(* Lemma and_le_pos : forall a b p,
  Pos.land a bd = N.pos p -> Pos.le b p.
Proof.
  intros a b. Print positive. induction b as [b' IHb'|b' IHb'|].
  - (* cbv [Pos.le Pos.compare Pos.compare_cont]. *) destruct p as [p'|p'|]; try lia.
    + destruct a as [a'|a'|].
      -- simpl. intros. (* cbv [Pos.Nsucc_double] in H. *) simpl. cbv [Pos.le Pos.compare]. simpl.
         apply IHb'. simpl. destruct b' as [b''|b''|].
        ++ simpl in H.
Lemma and_le : forall n m,
  Z.le 0 m -> Z.le 0 (Z.land n m) /\ Z.le (Z.land n m) m.
Proof.
  intros. cbv [Z.land]. destruct n as [| a| a]; destruct m as [| b| b]; split; try lia.
  - cbv [Z.of_N]. destruct (Pos.land a b) eqn:E; try lia. Search N.le.
    cbv [Z.le Z.compare]. Search Pos.land. Print Pos.le. Search Pos.compare.
Search Pos.land. Print Pos.land.

  -  *)


Lemma small_sum ctx s0 args' y: 
  interp_op ctx (add s0) args' = Some y -> 
   Z.le 0 y /\ Z.le y (Z.ones (Z.of_N s0)).
Proof.
  intros. simpl in H. injection H as H. split.
  - rewrite <- H. apply and_pos. apply Z.ones_nonneg. lia.
  - assert (H' : (0 <= Z.of_N s0)%Z) by lia. apply (Z.land_ones (fold_right Z.add 0%Z args')) in H'.
    rewrite H in H'. clear H. Check Z.mod_small. remember (fold_right Z.add 0%Z args') as sth. clear Heqsth. assert (H'' : (2 ^ Z.of_N s0 > 0)%Z).
    + lia.
    + Check Z_mod_lt. apply (Z_mod_lt sth) in H''. destruct H'' as [_ H'']. subst. cbv [Z.ones]. rewrite Z.shiftl_1_l. lia.
Qed.

Ltac inv H := inversion H; subst; clear H.

(* Lemma collapse_addition ctx d s0 i n args: 
  eval ctx d (ExprRef i) n ->
  dag.lookup d i = Some (add s0, args) ->
  eval ctx d (ExprApp (add s0, map ExprRef args)) n.
Proof.
  intros. Print interp_op. Print eval. Print eval. Print interp_op.
  inv H. rewrite H0 in H2. clear H0. injection H2; clear H2; intros; subst.
  apply EApp with (args' := args'); assumption.
Qed. *)

Lemma collapse_op ctx d i n op args: 
  eval ctx d (ExprRef i) n ->
  dag.lookup d i = Some (op, args) ->
  eval ctx d (ExprApp (op, map ExprRef args)) n.
Proof.
  intros. Print interp_op. Print eval. Print eval. Print interp_op.
  inv H. rewrite H0 in H2. clear H0. injection H2; clear H2; intros; subst.
  apply EApp with (args' := args'); assumption.
Qed.

Lemma collapse_op' ctx d i n op1 op2 args:
  eval ctx d (ExprApp (op1, [ExprRef i])) n ->
  dag.lookup d i = Some (op2, args) ->
  eval ctx d (ExprApp (op1, [ExprApp (op2, map ExprRef args)])) n.
Proof.
  intros. Print interp_op. Print eval. Print eval. Print interp_op.
  inv H. inv H3. apply (collapse_op _ _ _ _ _ _ H2) in H0. inv H6.
  apply EApp with (args' := [y]).
  - constructor.
    + assumption.
    + constructor.
  - assumption.
Qed.

(* Lemma collapse_additionZ ctx d i n args: 
  eval ctx d (ExprApp (addZ, [ExprRef i])) n ->
  dag.lookup d i = Some (addZ, args) ->
  eval ctx d (ExprApp (addZ, map ExprRef args)) n.
Proof.
  intros. Print interp_op. Print eval. Print eval. Print interp_op.
  inversion H. subst. inversion H3; subst. inversion H4; subst. rewrite H0 in H2.
  injection H2 as H2 H2'. subst. Print eval. inversion H7; subst.
  assert (E: interp_op ctx (addZ) [y] = Some y).
  - simpl. f_equal. rewrite Z.add_0_r. reflexivity.
  - rewrite E in H5. injection H5 as H5. subst. clear E. Print EApp. apply (EApp _ _ _ _ args').
    + apply H6.
    + apply H8.
Qed. *)

(* Lemma eval_list_of_addends (ctx : symbol -> option Z) (d : dag) (f : nat) (s : OperationSize):
  forall i n,
  eval ctx d (ExprApp (add s, [ExprRef i])) n ->
  eval ctx d (ExprApp (add s, map ExprRef (list_of_addends d f s i))) n.
Proof.
  induction f as [| f' IHf'].
  - intros. simpl. apply H.
  - intros. simpl. (* inversion H; subst. inversion H2; subst. inversion H3; subst. *)
    destruct (dag.lookup d i) as [ [o args]|] eqn:E1; try apply H.
    destruct o; try apply H.
    destruct (s =? s0)%N eqn:E; try apply H. apply N.eqb_eq in E. subst.
    apply (collapse_addition _ _ _ _ _ _ H) in E1. clear H.
    generalize dependent n. induction args as [| arg args1 IHargs1].
    + intros. simpl. simpl in E1. apply E1.
    + intros. simpl. rewrite map_app. apply break_add. *)

(* Worked with the previous version of eval_list_of_addends.

Lemma eval_list_of_addends (ctx : symbol -> option Z) (d : dag) (f : nat) (s : OperationSize):
  forall i n,
  eval ctx d (ExprApp (add s, [ExprRef i])) n ->
  eval ctx d (ExprApp (add s, map ExprRef (list_of_addends d f s i))) n.
Proof.
  induction f as [| f' IHf'].
  - intros. simpl. apply H.
  - intros. simpl. (* inversion H; subst. inversion H2; subst. inversion H3; subst. *)
    destruct (dag.lookup d i) as [ [o args]|] eqn:E1; try apply H.
    destruct o; try apply H.
    destruct (s =? s0)%N eqn:E; try apply H. apply N.eqb_eq in E. subst.
    apply (collapse_addition _ _ _ _ _ _ H) in E1. clear H.
    generalize dependent n. induction args as [| arg args1 IHargs1].
    + intros. simpl. simpl in E1. apply E1.
    + intros. simpl. rewrite map_app. simpl in E1. rewrite app_is_cons in E1.
      apply break_add_backwards in E1. destruct E1 as [m1 [m2 [E1 [E2 E3] ] ] ].
      Print break_add. apply (break_add m1 m2 n).
      -- apply E1.
      -- apply IHf'. apply E2.
      -- apply IHargs1. apply E3.
Qed. *)

Lemma mod_add_eq ctx d i n m s:
  eval ctx d (ExprRef i) n ->
  eval ctx d (ExprApp (add s, [ExprRef i])) m ->
  n mod 2 ^ Z.of_N s = m.
Proof.
  intros. simpl in H0. inv H0. inv H3. inv H6. Check eval_eval. apply (eval_eval _ _ _ _ H) in H2. clear H.
  subst. injection H5 as H5. subst. rewrite Z_land_ones'. f_equal. lia.
Qed.

Lemma mod_add_eq'' ctx d i n s:
  eval ctx d (ExprRef i) n ->
  eval ctx d (ExprApp (add s, [ExprRef i])) (n mod 2 ^ Z.of_N s).
Proof.
  intros. apply EApp with (args' := [n]).
  - constructor.
    + apply H.
    + constructor.
  - simpl. rewrite Z_land_ones'. f_equal. rewrite Z.add_0_r. reflexivity.
Qed.

(* Lemma mod_add_eq''_backwards ctx d i n s:
  eval ctx d (ExprApp (add s, [ExprRef i])) (n mod 2 ^ Z.of_N s) ->
  eval ctx d (ExprRef i) n.
Proof.
  intros. inv H. inv H2. inv H5. simpl in H4. injection H4 as H4. rewrite Z.add_0_r in H4. 
  rewrite Z_land_ones' in H4. apply EApp with (args' := [n]).
  - constructor.
    + apply H.
    + constructor.
  - simpl. rewrite Z_land_ones'. f_equal. rewrite Z.add_0_r. reflexivity.
Qed. *)

Lemma mod_add_eq_backwards ctx d i m s:
  eval ctx d (ExprApp (add s, [ExprRef i])) m ->
  exists n,
  eval ctx d (ExprRef i) n /\
  n mod 2 ^ Z.of_N s = m.
Proof.
  intros. inv H. inv H2. inv H5. exists y. split.
  - apply H1.
  - injection H4 as H4. rewrite <- H4. rewrite Z_land_ones'. f_equal; lia.
Qed. 

Lemma mod_addZ_eq_backwards ctx d i m:
  eval ctx d (ExprApp (addZ, [ExprRef i])) m ->
  exists n,
  eval ctx d (ExprRef i) n /\
  n = m.
Proof.
  intros. inv H. inv H2. inv H5. exists y. split.
  - apply H1.
  - injection H4 as H4. rewrite <- H4. lia.
Qed. 

Lemma mod_add_eq' ctx d n m s s0 args:
  N.le s s0 ->
  eval ctx d (ExprApp (add s, args)) m ->
  eval ctx d (ExprApp (add s0, args)) n ->
  n mod 2 ^ Z.of_N s = m.
Proof.
  intros. inv H0. inv H1. Search eval. apply (eval_eval_Forall2 _ _ _ _ H4) in H3. subst. clear H4.
  injection H6 as H6. injection H7 as H7. rewrite <- H6. rewrite <- H7. clear H6 H7.
  rewrite <- Z_land_ones'. rewrite <- Z.land_assoc. rewrite Z.land_ones_ones.
  replace (Z.of_N s0 <? 0) with false by lia. replace (Z.of_N s <? 0) with false by lia. simpl.
  replace (Z.min (Z.of_N s0) (Z.of_N s)) with (Z.of_N s) by lia. reflexivity.
Qed.

Lemma mod_add_eq''' ctx d n s s0 args:
  N.le s s0 ->
  eval ctx d (ExprApp (add s0, args)) n ->
  eval ctx d (ExprApp (add s, args)) (n mod 2 ^ Z.of_N s).
Proof.
  intros. inv H0. apply EApp with (args' := args').
  - assumption.
  - simpl. f_equal. injection H5 as H5; subst. clear H3.
    rewrite <- Z_land_ones'. rewrite <- Z.land_assoc. rewrite Z.land_ones_ones.
    replace (Z.of_N s0 <? 0) with false by lia. replace (Z.of_N s <? 0) with false by lia. simpl.
    replace (Z.min (Z.of_N s0) (Z.of_N s)) with (Z.of_N s) by lia. reflexivity.
Qed.

Lemma mod_addZ_eq''' ctx d n s args:
  eval ctx d (ExprApp (addZ, args)) n ->
  eval ctx d (ExprApp (add s, args)) (n mod 2 ^ Z.of_N s).
Proof.
  intros. inv H. apply EApp with (args' := args').
  - assumption.
  - simpl. f_equal. injection H4 as H4; subst. clear H2.
    rewrite <- Z_land_ones'. reflexivity.
Qed.

Lemma mod_add_eq'''_backwards ctx d n s s0 args:
  N.le s s0 ->
  eval ctx d (ExprApp (add s, args)) n ->
  exists m,
  eval ctx d (ExprApp (add s0, args)) m /\
  n = m mod (2 ^ Z.of_N s).
Proof.
  intros. inv H0. simpl in H5. exists (Z.land (fold_right Z.add 0 args') (Z.ones (Z.of_N s0))). split.
  - apply EApp with (args' := args').
    + assumption.
    + reflexivity.
  - rewrite <- Z_land_ones'. rewrite <- Z.land_assoc.
    repeat rewrite Z.land_ones_ones.
    replace (Z.of_N s0 <? 0) with false by lia. replace (Z.of_N s <? 0) with false by lia. simpl.
    replace (Z.min (Z.of_N s0) (Z.of_N s)) with (Z.of_N s) by lia.
    injection H5 as H5; subst. reflexivity.
Qed.

Lemma mod_addZ_eq'''_backwards ctx d n s args:
  eval ctx d (ExprApp (add s, args)) n ->
  exists m,
  eval ctx d (ExprApp (addZ, args)) m /\
  n = m mod (2 ^ Z.of_N s).
Proof.
  intros. inv H. simpl in H4. exists (fold_right Z.add 0 args'). split.
  - apply EApp with (args' := args').
    + assumption.
    + reflexivity.
  - injection H4 as H4; subst. rewrite <- Z_land_ones'. reflexivity.
Qed.

Lemma mod_addZ_eq' ctx d n m s args:
  eval ctx d (ExprApp (add s, args)) m ->
  eval ctx d (ExprApp (addZ, args)) n ->
  n mod 2 ^ Z.of_N s = m.
Proof.
  intros. inv H. inv H0. apply (eval_eval_Forall2 _ _ _ _ H2) in H3. subst. clear H2.
  injection H5 as H5. injection H6 as H6. rewrite <- H5. rewrite <- H6. clear H5 H6.
  rewrite <- Z_land_ones'. reflexivity.
Qed.


Lemma eval_list_of_addends' (ctx : symbol -> option Z) (d : dag) (f : nat) (s : OperationSize):
  forall i n m,
  eval ctx d (ExprRef i) n ->
  eval ctx d (ExprApp (add s, map ExprRef (list_of_addends d f s i))) m ->
  n mod (2 ^ Z.of_N s) = m.
Proof.
  induction f as [| f' IHf'].
  - intros. apply (mod_add_eq _ _ _ _ _ _ H H0).
  - intros. simpl in H0. destruct (dag.lookup d i) as [ [o args]|] eqn:E1; try apply (mod_add_eq _ _ _ _ _ _ H H0).
    + destruct o; try apply (mod_add_eq _ _ _ _ _ _ H H0).
      -- destruct (s <=? s0)%N eqn:E; try apply (mod_add_eq _ _ _ _ _ _ H H0). apply N.leb_le in E. subst.
         Check collapse_op. apply (collapse_op _ _ _ _ _ _ H) in E1. clear H.
         generalize dependent n. generalize dependent m. induction args as [| arg args1 IHargs1].
        ++ intros. simpl in E1. simpl in H0. apply (mod_add_eq' _ _ _ _ _ _ _ E H0 E1).
        ++ intros. simpl in H0. rewrite map_app in H0. apply break_add_backwards in H0.
           destruct H0 as [m1 [m2 [H1 [H2 H3] ] ] ]. simpl in E1. rewrite app_is_cons in E1.
           apply break_add_backwards in E1. destruct E1 as [n1 [n2 [H4 [H5 H6] ] ] ].
           apply (IHargs1 _ H3 _) in H6. clear H3 IHargs1. injection H4 as H4.
           injection H1 as H1. subst. apply mod_add_eq_backwards in H5. destruct H5 as [m1_ [H3 H4] ].
           apply (IHf' _ _ _ H3) in H2. clear IHf' H3. rewrite <- H2. rewrite <- H4.
           repeat rewrite Z_land_ones'.
           rewrite <- PullPush.Z.add_mod_l. repeat rewrite Z.add_0_r. rewrite <- PullPush.Z.add_mod_full.
           repeat rewrite <- Z_land_ones'. rewrite <- Z.land_assoc.

           repeat rewrite Z.land_ones_ones.
           replace (Z.of_N s0 <? 0) with false by lia. replace (Z.of_N s <? 0) with false by lia. simpl.
           replace (Z.min (Z.of_N s0) (Z.of_N s)) with (Z.of_N s) by lia.

           reflexivity.
      -- Check collapse_op. apply (collapse_op _ _ _ _ _ _ H) in E1. clear H.
         generalize dependent n. generalize dependent m. induction args as [| arg args1 IHargs1].
        ++ intros. simpl in E1. simpl in H0. apply (mod_addZ_eq' _ _ _ _ _ _ H0 E1).
        ++ intros. simpl in H0. rewrite map_app in H0. apply break_add_backwards in H0.
           destruct H0 as [m1 [m2 [H1 [H2 H3] ] ] ]. simpl in E1. rewrite app_is_cons in E1.
           apply break_addZ_backwards in E1. destruct E1 as [n1 [n2 [H4 [H5 H6] ] ] ].
           apply (IHargs1 _ H3 _) in H6. clear H3 IHargs1. injection H4 as H4.
           injection H1 as H1. subst. apply mod_addZ_eq_backwards in H5. destruct H5 as [m1_ [H3 H4] ].
           apply (IHf' _ _ _ H3) in H2. clear IHf' H3. rewrite <- H2. rewrite <- H4.
           repeat rewrite Z_land_ones'.
           rewrite <- PullPush.Z.add_mod_l. repeat rewrite Z.add_0_r. rewrite <- PullPush.Z.add_mod_r.
           reflexivity.
Qed.

Lemma eval_list_of_addends'' (ctx : symbol -> option Z) (d : dag) (f : nat) (s : OperationSize):
  forall i n,
  eval ctx d (ExprRef i) n ->
  eval ctx d (ExprApp (add s, map ExprRef (list_of_addends d f s i))) (n mod (2 ^ Z.of_N s)).
Proof.
  (* intros. Check mod_add_eq. apply mod_add_eq'' with (s := s) in H. generalize dependent H. *)
  induction f as [| f' IHf'].
  - intros. simpl. apply (mod_add_eq'' _ _ _ _ _ H).
  - intros. simpl. destruct (dag.lookup d i) as [ [o args]|] eqn:E1; try apply (mod_add_eq'' _ _ _ _ _ H).
    + destruct o; try apply (mod_add_eq'' _ _ _ _ _ H).
      -- destruct (s <=? s0)%N eqn:E; try apply (mod_add_eq'' _ _ _ _ _ H). apply N.leb_le in E.
         Check collapse_op. Check collapse_op. apply (collapse_op _ _ _ _ _ _ H) in E1. clear H.
         generalize dependent n. induction args as [| arg args1 IHargs1].
        ++ intros. simpl in E1. simpl. Check mod_add_eq'''. apply (mod_add_eq''' _ _ _ _ _ _ E E1).
        ++ intros. simpl. rewrite map_app. simpl in E1. rewrite app_is_cons in E1.
           apply break_add_backwards in E1. destruct E1 as [n1 [n2 [H4 [H5 H6] ] ] ].
           injection H4 as H4; subst. Check break_add. Check mod_add_eq'''.
           apply (mod_add_eq''' _ _ _ _ _ _ E) in H5. apply (mod_add_eq''' _ _ _ _ _ _ E) in H6.
           apply mod_add_eq_backwards in H5. destruct H5 as [n1' [H5 H5'] ].
           Check mod_add_eq'''. apply (mod_add_eq'''_backwards _ _ _ _ _ _ E) in H6.
           destruct H6 as [n2' [H6 H6'] ].
           Check break_add. apply (break_add (n1' mod 2 ^ Z.of_N s) (n2' mod (2 ^ Z.of_N s))).
           --- simpl. f_equal. repeat rewrite Z_land_ones'. repeat rewrite Z.add_0_r. rewrite <- Zplus_mod.
               repeat rewrite <- Z_land_ones'. rewrite <- Z.land_assoc.
               repeat rewrite Z.land_ones_ones.
           replace (Z.of_N s0 <? 0) with false by lia. replace (Z.of_N s <? 0) with false by lia. simpl.
           replace (Z.min (Z.of_N s0) (Z.of_N s)) with (Z.of_N s) by lia.
  
           repeat rewrite Z_land_ones'. rewrite Zplus_mod. rewrite H5'. rewrite <- H6'. (*  rewrite Z.mod_mod by lia.  *)rewrite <- Zplus_mod. reflexivity. 
           --- apply IHf'. apply H5.
           --- apply IHargs1. Check mod_add_eq. Check mod_add_eq'. Check mod_add_eq''. Check mod_add_eq'''. Check mod_add_eq_backwards. apply H6.
      -- Check collapse_op. Check collapse_op. apply (collapse_op _ _ _ _ _ _ H) in E1. clear H.
         generalize dependent n. induction args as [| arg args1 IHargs1].
        ++ intros. simpl in E1. simpl. Check mod_add_eq'''. apply (mod_addZ_eq''' _ _ _ _ _ E1).
        ++ intros. simpl. rewrite map_app. simpl in E1. rewrite app_is_cons in E1.
           apply break_addZ_backwards in E1. destruct E1 as [n1 [n2 [H4 [H5 H6] ] ] ].
           injection H4 as H4; subst. Check break_add. Check mod_addZ_eq'''.
           apply mod_addZ_eq''' with (s := s) in H5. apply mod_addZ_eq''' with (s := s) in H6.
           apply mod_add_eq_backwards in H5. destruct H5 as [n1' [H5 H5'] ].
           Check mod_add_eq'''_backwards. apply (mod_addZ_eq'''_backwards) in H6.
           destruct H6 as [n2' [H6 H6'] ].
           Check break_add. apply (break_add (n1' mod 2 ^ Z.of_N s) (n2' mod (2 ^ Z.of_N s))).
           --- simpl. f_equal. repeat rewrite Z_land_ones'. repeat rewrite Z.add_0_r. rewrite H5'. rewrite <- H6'. rewrite <- Zplus_mod.
               reflexivity. 
           --- apply IHf'. apply H5.
           --- apply IHargs1. Check mod_add_eq. Check mod_add_eq'. Check mod_add_eq''. Check mod_add_eq'''. Check mod_add_eq_backwards. apply H6.
Qed.

(*  Check break_add_backwards.  Check break_add. apply break_add.
           destruct H0 as [m1 [m2 [H1 [H2 H3] ] ] ].
           apply (IHargs1 _ H3 _) in H6. clear H3 IHargs1. injection H4 as H4.
           injection H1 as H1. subst. apply mod_add_eq_backwards in H5. destruct H5 as [m1_ [H3 H4] ].
           apply (IHf' _ _ _ H3) in H2. clear IHf' H3. rewrite <- H2. rewrite <- H4.
           repeat rewrite Z_land_ones'.
           rewrite <- PullPush.Z.add_mod_l. repeat rewrite Z.add_0_r. rewrite <- PullPush.Z.add_mod_full.
           repeat rewrite <- Z_land_ones'. rewrite <- Z.land_assoc.

           repeat rewrite Z.land_ones_ones.
           replace (Z.of_N s0 <? 0) with false by lia. replace (Z.of_N s <? 0) with false by lia. simpl.
           replace (Z.min (Z.of_N s0) (Z.of_N s)) with (Z.of_N s) by lia.

           reflexivity.
      -- Check collapse_op. apply (collapse_op _ _ _ _ _ _ H) in E1. clear H.
         generalize dependent n. generalize dependent m. induction args as [| arg args1 IHargs1].
        ++ intros. simpl in E1. simpl in H0. apply (mod_addZ_eq' _ _ _ _ _ _ H0 E1).
        ++ intros. simpl in H0. rewrite map_app in H0. apply break_add_backwards in H0.
           destruct H0 as [m1 [m2 [H1 [H2 H3] ] ] ]. simpl in E1. rewrite app_is_cons in E1.
           apply break_addZ_backwards in E1. destruct E1 as [n1 [n2 [H4 [H5 H6] ] ] ].
           apply (IHargs1 _ H3 _) in H6. clear H3 IHargs1. injection H4 as H4.
           injection H1 as H1. subst. apply mod_addZ_eq_backwards in H5. destruct H5 as [m1_ [H3 H4] ].
           apply (IHf' _ _ _ H3) in H2. clear IHf' H3. rewrite <- H2. rewrite <- H4.
           repeat rewrite Z_land_ones'.
           rewrite <- PullPush.Z.add_mod_l. repeat rewrite Z.add_0_r. rewrite <- PullPush.Z.add_mod_r.
           reflexivity.
Qed. *)


(* Lemma eval_list_of_addends' (ctx : symbol -> option Z) (d : dag) (f : nat) (s : OperationSize):
  forall i n m,
  eval ctx d (ExprRef i) n ->
  0 <= n <= (2 ^ Z.of_N s - 1) ->
  eval ctx d (ExprApp (add s, map ExprRef (list_of_addends d f s i))) m ->
  n = m.
Proof.
  induction f as [| f' IHf'].
  - intros. apply (mod_add_eq _ _ _ _ _ _ H H0).
  - intros. simpl in H0. destruct (dag.lookup d i) as [ [o args]|] eqn:E1; try apply (mod_add_eq _ _ _ _ _ _ H H0).
    + destruct o; try apply (mod_add_eq _ _ _ _ _ _ H H0).
      -- destruct (s <=? s0)%N eqn:E; try apply (mod_add_eq _ _ _ _ _ _ H H0). apply N.leb_le in E. subst.
         Check collapse_op. apply (collapse_op _ _ _ _ _ _ H) in E1. clear H.
         generalize dependent n. generalize dependent m. induction args as [| arg args1 IHargs1].
        ++ intros. simpl in E1. simpl in H0. apply (mod_add_eq' _ _ _ _ _ _ _ E H0 E1).
        ++ intros. simpl in H0. rewrite map_app in H0. apply break_add_backwards in H0.
           destruct H0 as [m1 [m2 [H1 [H2 H3] ] ] ]. simpl in E1. rewrite app_is_cons in E1.
           apply break_add_backwards in E1. destruct E1 as [n1 [n2 [H4 [H5 H6] ] ] ].
           apply (IHargs1 _ H3 _) in H6. clear H3 IHargs1. injection H4 as H4.
           injection H1 as H1. subst. apply mod_add_eq_backwards in H5. destruct H5 as [m1_ [H3 H4] ].
           apply (IHf' _ _ _ H3) in H2. clear IHf' H3. rewrite <- H2. rewrite <- H4.
           repeat rewrite Z_land_ones'.
           rewrite <- PullPush.Z.add_mod_l. repeat rewrite Z.add_0_r. rewrite <- PullPush.Z.add_mod_full.
           repeat rewrite <- Z_land_ones'. rewrite <- Z.land_assoc.

           repeat rewrite Z.land_ones_ones.
           replace (Z.of_N s0 <? 0) with false by lia. replace (Z.of_N s <? 0) with false by lia. simpl.
           replace (Z.min (Z.of_N s0) (Z.of_N s)) with (Z.of_N s) by lia.

           reflexivity.
      -- Check collapse_op. apply (collapse_op _ _ _ _ _ _ H) in E1. clear H.
         generalize dependent n. generalize dependent m. induction args as [| arg args1 IHargs1].
        ++ intros. simpl in E1. simpl in H0. apply (mod_addZ_eq' _ _ _ _ _ _ H0 E1).
        ++ intros. simpl in H0. rewrite map_app in H0. apply break_add_backwards in H0.
           destruct H0 as [m1 [m2 [H1 [H2 H3] ] ] ]. simpl in E1. rewrite app_is_cons in E1.
           apply break_addZ_backwards in E1. destruct E1 as [n1 [n2 [H4 [H5 H6] ] ] ].
           apply (IHargs1 _ H3 _) in H6. clear H3 IHargs1. injection H4 as H4.
           injection H1 as H1. subst. apply mod_addZ_eq_backwards in H5. destruct H5 as [m1_ [H3 H4] ].
           apply (IHf' _ _ _ H3) in H2. clear IHf' H3. rewrite <- H2. rewrite <- H4.
           repeat rewrite Z_land_ones'.
           rewrite <- PullPush.Z.add_mod_l. repeat rewrite Z.add_0_r. rewrite <- PullPush.Z.add_mod_r.
           reflexivity.
Qed.

 *)
(* 
Lemma eval_list_of_addends' (ctx : symbol -> option Z) (d : dag) (f : nat) (s : OperationSize):
  forall i n,
  is_bounded_by (ExprRef i) 
  eval ctx d (ExprRef i) n ->
  eval ctx d (ExprApp (add s, map ExprRef (list_of_addends d f s i))) n.
Proof.
  induction f as [| f' IHf'].
  - intros. simpl. apply H.
  - intros. simpl. (* inversion H; subst. inversion H2; subst. inversion H3; subst. *)
    destruct (dag.lookup d i) as [ [o args]|] eqn:E1; try apply H.
    destruct o; try apply H.
    destruct (s =? s0)%N eqn:E; try apply H. apply N.eqb_eq in E. subst.
    apply (collapse_addition _ _ _ _ _ _ H) in E1. clear H.
    generalize dependent n. induction args as [| arg args1 IHargs1].
    + intros. simpl. simpl in E1. apply E1.
    + intros. simpl. rewrite map_app. simpl in E1. rewrite app_is_cons in E1.
      apply break_add_backwards in E1. destruct E1 as [m1 [m2 [E1 [E2 E3] ] ] ].
      Print break_add. apply (break_add m1 m2 n).
      -- apply E1.
      -- apply IHf'. apply E2.
      -- apply IHargs1. apply E3.
Qed. *)

(* Lemma evalZ_list_of_addends (ctx : symbol -> option Z) (d : dag) (f : nat) (s : OperationSize):
  forall i n,
  eval ctx d (ExprApp (addZ, [ExprRef i])) n ->
  eval ctx d (ExprApp (addZ, map ExprRef (list_of_addends d f s i))) n.
Proof.
  induction f as [| f' IHf'].
  - intros. simpl. apply H.
  - intros. simpl. (* inversion H; subst. inversion H2; subst. inversion H3; subst. *)
    destruct (dag.lookup d i) as [ [o args]|] eqn:E1; try apply H.
    destruct o; try apply H.
    destruct (s =? s0)%N eqn:E; try apply H. apply N.eqb_eq in E. subst.
    apply (collapse_additionZ _ _ _ _ _ H) in E1. clear H.
    generalize dependent n. induction args as [| arg args1 IHargs1].
    + intros. simpl. simpl in E1. apply E1.
    + intros. simpl. rewrite map_app. simpl in E1. rewrite app_is_cons in E1.
      apply break_add_backwards in E1. destruct E1 as [m1 [m2 [E1 [E2 E3] ] ] ].
      Print break_add. apply (break_add m1 m2 n).
      -- apply E1.
      -- apply IHf'. apply E2.
      -- apply IHargs1. apply E3.
Qed. *)

(* Search 

  simpl in H8. injection H5 as H5. injection H8 as H8.
  remember (interp_op ctx o assert (E: eval ctx d (ExprRef i) ) 
    + Print eval. assert (E': Forall2 (eval ctx d) (map ExprRef []) []). { apply Forall2_nil. }
      Print eval. apply (ERef _ _ _ _ _ _ _ H0 E'). reflexivity.
    + assert (E': eval ctx d (ExprApp (add s0, [ExprRef i])) 0).
      -- Print eval. apply (EApp _ _ _ _ [0]%Z).
        ++ apply Forall2_cons.
          --- apply E.
          --- apply Forall2_nil.
        ++ reflexivity.
      -- Search eval. assert (E'': n = 0%Z).
        ++ Print eval_eval. apply (eval_eval ctx d (ExprApp (add s0, [ExprRef i])) _ H _ E').
        ++ rewrite E''. Print eval. apply (EApp _ _ _ _ []).
          --- apply Forall2_nil.
          --- reflexivity.

















generalize dependent H0. generalize dependent H. induction args as [| arg args1 IHargs1].
  - intros. simpl. Print interp_op. Print eval. Print eval. assert (E: eval ctx d (ExprRef i) 0). 
    + Print eval. assert (E': Forall2 (eval ctx d) (map ExprRef []) []). { apply Forall2_nil. }
      Print eval. apply (ERef _ _ _ _ _ _ _ H0 E'). reflexivity.
    + assert (E': eval ctx d (ExprApp (add s0, [ExprRef i])) 0).
      -- Print eval. apply (EApp _ _ _ _ [0]%Z).
        ++ apply Forall2_cons.
          --- apply E.
          --- apply Forall2_nil.
        ++ reflexivity.
      -- Search eval. assert (E'': n = 0%Z).
        ++ Print eval_eval. apply (eval_eval ctx d (ExprApp (add s0, [ExprRef i])) _ H _ E').
        ++ rewrite E''. Print eval. apply (EApp _ _ _ _ []).
          --- apply Forall2_nil.
          --- reflexivity.
  - intros. simpl.
        
    Print eval. apply (EApp _ _ _ _ []).
    + constructor.
    + 
inversion H; subst. simpl in H5. inversion H5; subst. inversion H3; subst. inversion H7; subst. clear H7.
  


    generalize dependent E1. generalize dependent n. generalize dependent i.
    induction args as [| arg args' IHargs'].
    2: {
    intros.
    
    apply IHf' in H.



    simpl. inversion H; subst. inversion H2; subst. inversion H3; subst. rewrite E1 in H1.
    injection H1 as H1 H1'. subst. simpl in H7. clear H4 H2 H3 H6 E1 l' i H. generalize dependent args'. (* inversion H5; subst. simpl in H7. injection H7 as H7. *)

    induction args's as [| arg args' IHargs'].
    + simpl. inversion H; subst. inversion H2; subst. inversion H3; subst. rewrite E1 in H1.
      injection H1 as H1 H1'. subst. inversion H5; subst. simpl in H7. injection H7 as H7.
      Search eval. Print eval_node.
      inversion H6. subst. simpl in H4. injection H4 as H4. subst.
      apply (EApp _ _ _ _ []).
      -- constructor.
      -- reflexivity.
    + 
    induction args0 as [| args args0' IHargs0']. 2: {
    generalize dependent args'. generalize dependent i. generalize dependent n.
    induction args0 as [| arg args0' IHargs0'].
    + intros. simpl.
      inversion H2; subst. inversion H3; subst. rewrite E1 in H1. injection H1 as H1 H1'. subst.
      inversion H5; subst. simpl in H7. injection H7 as H7.
      inversion H6. subst. simpl in H4. injection H4 as H4. subst.
      Print eval. apply (EApp _ _ _ _ []).
      -- constructor.
      -- reflexivity.
    + intros. simpl. Search eval. Print eval. simpl. apply IHf' in H. inversion H5; subst.
      simpl in H7. *)


Print N.
Print positive.

Search (N -> nat).
Search (N -> N -> bool).

Fixpoint withadc_without (d : dag) (s : OperationSize) (args : list idx) : (list (list (list idx))) * (list idx) :=
  match args with
  | [] => ([], [])
  | i :: args' =>
    let (withadc', without') := withadc_without d s args' in
    match dag.lookup d i with
    | Some (o, args'') =>
      match o, args'' with
      | addcarry s', (x :: y :: []) => 
        if N.eqb s' s && fold_right andb true (map (is_bounded_by d (2 ^ Z.of_N s - 1)) [x; y]) then
          (map (list_of_addends d (N.to_nat (dag.size d)) s) [x; y] :: withadc', without')
        else
          (withadc', i :: without')
      | _, _ => (withadc', i :: without')
      end
    | None => (withadc', i :: without')
    end
  end.

Print interp_op.

Definition keep n x := Z.land x (Z.ones (Z.of_N n)).
Print Z.shiftr. Print Z.shiftl.

Print expr.

Definition expr_of_a_carry (s : OperationSize) (carry : list (list idx)) : expr :=
  let with_small_adds := map (fun addends => ExprApp (add s, map ExprRef addends)) carry in
  ExprApp (shrZ, [ExprApp (addZ, with_small_adds); ExprApp (const (Z.of_N s), [])]).

Print interp_op.

(* Lemma eval_expr_of_a_carry ctx d s f arg1 arg2 n1 n2 : 
  eval ctx d (expr_of_a_carry s (map (list_of_addends d f s) [arg1; arg2])) n1 ->
  eval ctx d (ExprApp (addcarry s, map (fun i => ExprApp (add s, [ExprRef i])) [arg1; arg2])) n2 ->
  n1 = n2.
Proof.
  simpl. cbv [expr_of_a_carry]. simpl. intros. inv H. inv H0.
  simpl in H5. destruct args' as [| a [| b [| c] ] ]; try discriminate H5. inv H3.
  inv H4. inv H1. inv H8. inv H4. inv H9. inv H1. injection H10 as H10; subst. clear H11.
  inv H12. inv H2. inv H9. inv H10. injection H5 as H5; subst. injection H6 as H6; subst. 
  injection H7 as H7; subst. Check eval_list_of_addends. apply eval_list_of_addends with (f := f) in H1.
  apply eval_list_of_addends with (f := f) in H2.
  Check eval_eval. apply (eval_eval _ _ _ _ H3) in H1. apply (eval_eval _ _ _ _ H2) in H4.
  subst. rewrite Z.add_0_r. inv H3. clear H1. inv H2. clear H1. Check small_sum. apply small_sum in H5.
  apply small_sum in H4. repeat rewrite Z.shiftr_div_pow2; try lia. Search (_ + _ <= _ + _)%Z.
  destruct H5 as [H5' H5]. destruct H4 as [H4' H4]. Check Z.add_le_mono. apply (Z.add_le_mono _ _ _ _ H5) in H4.
  cbv [Z.ones] in H4. repeat rewrite Z.shiftl_1_l in H4. assert (E : y1 + y0 < 2 * (2 ^ Z.of_N s)) by lia.
  Check Z.div_lt_upper_bound. assert ((y1 + y0) / 2 ^ Z.of_N s < 2).
  - apply Z.div_lt_upper_bound; lia.
  - apply (Z.add_le_mono _ _ _ _ H5') in H4'. Check Z.mod_small.
    symmetry. apply Z.mod_small. split.
    + Search Z.div. apply Z.div_pos.
      -- apply H4'.
      -- lia.
    + apply H.
Qed.
 *)

Local Open Scope Z_scope.

Require Import coqutil.Tactics.autoforward coqutil.Decidable coqutil.Tactics.Tactics.
Global Set Default Goal Selector "1".

Import coqutil.Tactics.Tactics.
Ltac t:= match goal with
  | _ => progress intros
  | H : eval _ _ (ExprApp _) _ |- _ => inversion H; clear H; subst
  | H : Forall _ (cons _ _) |- _ => inversion H; clear H; subst
  | H : Forall _ nil |- _ => inversion H; clear H; subst
  | H : Forall2 _ (cons _ _) _ |- _ => inversion H; clear H; subst
  | H : Forall2 _ nil _ |- _ => inversion H; clear H; subst
  | H : Forall2 _ _ (cons _ _) |- _ => inversion H; clear H; subst
  | H : Forall2 _ _ nil |- _ => inversion H; clear H; subst
  | H : _ = true |- _ => autoforward with typeclass_instances in H
  | H : forall b, _ |- _ => pose proof (H _ ltac:(eassumption) _ _ ltac:(eassumption)); clear H
  | H : eval _ ?d ?e ?v1, G: eval _ ?d ?e ?v2 |- _ =>
      assert_fails (constr_eq v1 v2);
      eapply (eval_eval _ d e v1 H v2) in G
  | _ => progress cbv [interp_op] in *
  | _ => progress cbn [fst snd] in *
  | _ => progress destruct_one_match
  | _ => progress Option.inversion_option
  | _ => progress subst
  end.

Lemma bound_sum' G d
  es (He : Forall (fun e => forall b, bound_expr e = Some b ->
       forall (d : dag) (v : Z), eval G d e v -> (0 <= v <= b)%Z) es)
  : forall
  bs (Hb : Option.List.lift (map bound_expr es) = Some bs)
  vs (Hv : Forall2 (eval G d) es vs)
  , (0 <= fold_right Z.add 0 vs <= fold_right Z.add 0 bs)%Z.
Proof using Type.
  induction He; cbn in *; repeat t.
  { cbv [fold_right]; Lia.lia. }
  destruct (bound_expr _) eqn:? in *; cbn in *; repeat t.
  destruct (fold_right (B:=option _) _) eqn:? in *; cbn in *; repeat t.
  specialize (IHHe _ ltac:(eassumption) _ ltac:(eassumption)); cbn.
  specialize (H _ ltac:(exact eq_refl) _ _ ltac:(eassumption)).
  Lia.lia.
Qed.

Lemma eval_bound_expr G e b : bound_expr e = Some b ->
  forall d v, eval G d e v -> (0 <= v <= b)%Z.
Proof using Type.
  revert b; induction e; simpl bound_expr; BreakMatch.break_match;
    inversion 2; intros; inversion_option; subst;
    try match goal with H : context [set_slice] |- _ => shelve end;
    cbv [interp_op] in *;
    BreakMatch.break_match_hyps; inversion_option; subst;
    rewrite ?Z.ldiff_ones_r, ?Z.land_ones, ?Z.ones_equiv;
    cbv [Z.b2z];
    try match goal with |- context [(?a mod ?b)%Z] => unshelve epose proof Z.mod_pos_bound a b ltac:(eapply Z.pow_pos_nonneg; Lia.lia) end;
    repeat t;
    try (Z.div_mod_to_equations; Lia.lia).
  { clear dependent args'0.
    epose proof bound_sum' _ ltac:(eassumption) _ ltac:(eassumption) _ ltac:(eassumption) _ ltac:(eassumption).
    split; try Lia.lia.
    eapply Z.min_glb_iff; split; try Lia.lia.
    etransitivity. eapply Zmod_le.
    all : try Lia.lia. }
  Unshelve. {
    repeat t.
    pose proof Z.log2_nonneg z; pose proof Z.log2_nonneg z0.
    rewrite !Z.shiftl_0_r.
    split.
    { eapply Z.lor_nonneg; split; try eapply Z.land_nonneg; try eapply Z.ldiff_nonneg; Lia.lia. }
    eapply Z.le_bitwise.
    { eapply Z.lor_nonneg; split; try eapply Z.land_nonneg; try eapply Z.ldiff_nonneg; Lia.lia. }
    { eapply Z.lor_nonneg; split; try eapply Z.land_nonneg; try eapply Z.ldiff_nonneg;
        left; try eapply Z.ones_nonneg; Lia.lia. }
    { intros i Hi.
      Z.rewrite_bitwise.
      destr (i <? Z.of_N sz);
        rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_l, ?Bool.orb_false_r.
      { clear -H Hi.
        destr (i <? Z.succ (Z.log2 z0)).
        { eapply Bool.le_implb, Bool.implb_true_r. }
        rewrite Z.bits_above_log2; cbn; trivial; try Lia.lia.
        destruct H as [H' H]; eapply Z.log2_le_mono in H. Lia.lia. }
      { clear -H0 Hi.
        destr (i <? Z.succ (Z.log2 z)).
        { eapply Bool.le_implb, Bool.implb_true_r. }
        rewrite Z.bits_above_log2; cbn; trivial; try Lia.lia.
        destruct H0 as [? H0]; eapply Z.log2_le_mono in H0. Lia.lia. } } }
Qed.

Lemma eval_is_bounded_by ctx d m x i :
  is_bounded_by d m i = true ->
  eval ctx d (ExprRef i) x ->
  0 <= x <= m.
Proof.
  intros. cbv [is_bounded_by] in H. destruct (bound_expr _) as [b|] eqn:E; try discriminate H.
  Check eval_bound_expr. Search reveal. assert (H0': eval ctx d (reveal d 1 i) x) by eauto using eval_reveal.
  clear H0. Check eval_bound_expr. assert (H1 : 0 <= x <= b) by eauto using eval_bound_expr. lia.
Qed.

Lemma eval_expr_of_a_carry' ctx d s f arg1 arg2 n1 n2 :
  is_bounded_by d (2 ^ Z.of_N s - 1) arg1 = true ->
  is_bounded_by d (2 ^ Z.of_N s - 1) arg2 = true ->
  eval ctx d (expr_of_a_carry s (map (list_of_addends d f s) [arg1; arg2])) n1 ->
  eval ctx d (ExprApp (addcarry s, map ExprRef [arg1; arg2])) n2 ->
  n1 = n2.
Proof.
  simpl. intros E1 E2. cbv [expr_of_a_carry]. simpl. intros. inv H. inv H0.
  simpl in H5. destruct args' as [| a [| b [| c] ] ]; try discriminate H5. inv H3.
  inv H4. inv H1. inv H8. inv H4. inv H9. inv H1. injection H10 as H10; subst. clear H11.
  inv H12. inv H2. inv H9. inv H10. injection H5 as H5; subst. injection H6 as H6; subst. 
  injection H7 as H7; subst. Check eval_list_of_addends'.
  remember (eval_list_of_addends' _ _ _ _ _ _ _ H1 H3) as H eqn:E3.
  remember (eval_list_of_addends' _ _ _ _ _ _ _ H2 H4) as H' eqn:E4.
  clear E3 E4. apply (eval_is_bounded_by _ _ _ _ _ E1) in H1. apply (eval_is_bounded_by _ _ _ _ _ E2) in H2.
  clear E1 E2. repeat rewrite Z.add_0_r.
  inv H3. Check small_sum. apply small_sum in H8. clear H6. destruct H8 as [H8 H8'].
  inv H4. apply small_sum in H6. clear H3. destruct H6 as [H6 H6'].
  Check Z.add_le_mono. apply (Z.add_le_mono _ _ _ _ H8') in H6'. clear H8'.
  remember (y1 mod 2 ^ Z.of_N s) as y1' eqn:E1. remember (y2 mod 2 ^ Z.of_N s) as y2' eqn:E2.
  rewrite Z.mod_small in E1 by lia. rewrite Z.mod_small in E2 by lia. subst.
  cbv [Z.ones] in H6'. repeat rewrite Z.shiftl_1_l in H6'.
  assert (E : y1 + y2 < 2 * (2 ^ Z.of_N s)) by lia. assert ((y1 + y2) / 2 ^ Z.of_N s < 2).
  { apply Z.div_lt_upper_bound; lia. }
  Check Z.mod_small. repeat rewrite Z.shiftr_div_pow2 by lia. symmetry. apply Z.mod_small. split.
  - Search Z.div. apply Z.div_pos; lia.
  - lia.
Qed.

Lemma eval_expr_of_a_carry'' ctx d s f arg1 arg2 n :
  is_bounded_by d (2 ^ Z.of_N s - 1) arg1 = true ->
  is_bounded_by d (2 ^ Z.of_N s - 1) arg2 = true ->
  eval ctx d (ExprApp (addcarry s, map ExprRef [arg1; arg2])) n ->
  eval ctx d (expr_of_a_carry s (map (list_of_addends d f s) [arg1; arg2])) n.
Proof.
  simpl. intros E1 E2. cbv [expr_of_a_carry]. simpl. intros. inv H.
  inv H2. inv H5. inv H6. Check eval_list_of_addends''.
  Check eval_is_bounded_by.
  remember (eval_is_bounded_by _ _ _ _ _ E1 H1) as E1'. clear HeqE1' E1.
  remember (eval_is_bounded_by _ _ _ _ _ E2 H2) as E2'. clear HeqE2' E2.
  apply eval_list_of_addends'' with (s := s) (f := f) in H1.
  apply eval_list_of_addends'' with (s := s) (f := f) in H2.
  apply EApp with (args' := [(y mod 2 ^ Z.of_N s) + (y0 mod 2 ^ Z.of_N s); Z.of_N s]).
  - apply Forall2_cons.
    + apply EApp with (args' := [y mod 2 ^ Z.of_N s; y0 mod 2 ^ Z.of_N s]).
      -- apply Forall2_cons.
        ++ apply H1.
        ++ apply Forall2_cons.
          --- apply H2.
          --- apply Forall2_nil.
      -- simpl. f_equal. lia.
    + apply Forall2_cons.
      -- apply EApp with (args' := []).
        ++ apply Forall2_nil.
        ++ simpl. reflexivity.
      -- apply Forall2_nil.
  - simpl. f_equal. injection H4 as H4; subst. rewrite Z.add_0_r. repeat rewrite Z.mod_small by lia.
    destruct E1' as [E1 E1']. destruct E2' as [E2 E2'].
    assert (E : y + y0 < 2 * (2 ^ Z.of_N s)) by lia. assert ((y + y0) / 2 ^ Z.of_N s < 2).
    { apply Z.div_lt_upper_bound; lia. }
    repeat rewrite Z.shiftr_div_pow2 by lia. symmetry. apply Z.mod_small. split.
    + apply Z.div_pos; lia.
    + apply H.
Qed.


(*   destruct args' as [| a [| b [| c] ] ]; try discriminate H4. inv H2.
  inv H6. inv H2. inv H1. injection H4 as H4; subst. injection H6 as H6; subst.
  inv H3. inv H1. inv H5. inv H6. injection H4 as H4; subst. clear H7.
  Check eval_list_of_addends''.
  remember (eval_list_of_addends' _ _ _ _ _ _ _ H1 H3) as H eqn:E3.
  remember (eval_list_of_addends' _ _ _ _ _ _ _ H2 H4) as H' eqn:E4.
  clear E3 E4. apply (eval_is_bounded_by _ _ _ _ _ E1) in H1. apply (eval_is_bounded_by _ _ _ _ _ E2) in H2.
  clear E1 E2. repeat rewrite Z.add_0_r.
  inv H3. Check small_sum. apply small_sum in H8. clear H6. destruct H8 as [H8 H8'].
  inv H4. apply small_sum in H6. clear H3. destruct H6 as [H6 H6'].
  Check Z.add_le_mono. apply (Z.add_le_mono _ _ _ _ H8') in H6'. clear H8'.
  remember (y1 mod 2 ^ Z.of_N s) as y1' eqn:E1. remember (y2 mod 2 ^ Z.of_N s) as y2' eqn:E2.
  rewrite Z.mod_small in E1 by lia. rewrite Z.mod_small in E2 by lia. subst.
  cbv [Z.ones] in H6'. repeat rewrite Z.shiftl_1_l in H6'.
  assert (E : y1 + y2 < 2 * (2 ^ Z.of_N s)) by lia. assert ((y1 + y2) / 2 ^ Z.of_N s < 2).
  { apply Z.div_lt_upper_bound; lia. }
  Check Z.mod_small. repeat rewrite Z.shiftr_div_pow2 by lia. symmetry. apply Z.mod_small. split.
  - Search Z.div. apply Z.div_pos; lia.
  - lia.
Qed. *)

(* Definition expr_bounded_by m e : bool :=
  match bound_expr e with 
  | None => false
  | Some b => b <=? m
  end.

Definition bounded_by ctx d m e : Prop := forall x,
  eval ctx d e x ->
  0 <= x <= m.

Lemma expr_carry_bounded ctx d s arg1 arg2 x:
  eval ctx d (expr_of_a_carry s (map (list_of_addends d f s) [arg1; arg2])) x ->
  0 <= x <= 2 ^ Z.of_N s - 1.
Proof.
  intros. cbv [expr_of_a_carry] in H. remember (ExprApp (addZ, _)) as e. inv H. simpl in H4.
  destruct args' as [| a [| b [| c] ] ]; try discriminate H4. injection H4 as H4; subst.
  remember (map _ _) as e. inv H2. inv H5. inv H2. inv H1. inv H5. clear H6. remember (map _ _) as e.
  inv H3. injection H4 as H4; subst.
  inversion H; try discriminate Heqe. subst. cbv [map] in H. cbv [expr_of_a_carry] in H. Print bound_expr. inv H.

(*  *)

  clear E3 E4 H1 H2. inv H3. apply small_sum in H6. clear H2. inv H4. apply small_sum in H3. clear H1.
  destruct H3 as [H3 H3']. destruct H6 as [H6 H6']. repeat rewrite Z.add_0_r.

  Check Z.add_le_mono. apply (Z.add_le_mono _ _ _ _ H6') in H3'. clear H6'. cbv [Z.ones] in H3'.
  repeat rewrite Z.shiftl_1_l in H3'. remember (y1 mod 2 ^ Z.of_N s) as y1'. remember (y2 mod 2 ^ Z.of_N s) as y2'.
  assert (E : y1' + y2' < 2 * (2 ^ Z.of_N s)) by lia. assert ((y1' + y2') / 2 ^ Z.of_N s < 2).
  - apply Z.div_lt_upper_bound; lia.
  - Check Z.add_le_mono. apply (Z.add_le_mono _ _ _ _ H6) in H3. clear H6. Check Z.mod_small. symmetry.
    subst. Search Z.testbit. Search Z.land. Search Z.modulo. Search Z.land. Check Z.shiftr_land.
    Search ((_ mod _) / _). Search Z.shiftr. Search (_ mod 2). Search ((_ + _) / _).
    rewrite Z.shiftr_div_pow2 by lia. rewrite Div.Z.div_add_mod_cond_l by lia.
    rewrite Div.Z.div_add_mod_cond_r by lia.






    assert (H': (y1 mod 2 ^ Z.of_N s + y2 mod 2 ^ Z.of_N s) = (y1 + y2) mod (2 ^ Z.of_N (s + 1))). 
    + Check Z.mod_small.  
      rewrite <- Z.pow_succ_r in E by lia. simpl in E.
      Search (Z.succ (Z.of_N _)). rewrite <- N2Z.inj_succ in E. rewrite <- (Z.mod_small ((y1 mod _) + _) (2 ^ Z.of_N (s + 1))) by lia.
    rewrite <- (Z.mod_small ((y1 mod _) + _) (2 ^ Z.of_N (s + 1))) by lia.
    Check Z.add_mod. rewrite Z.add_mod by lia. repeat rewrite <- Z_land_ones'. Check Z.land_assoc.
    repeat rewrite <- (Z.land_assoc _ _ (Z.ones (Z.of_N (s + 1)))).

Search Z.shiftr.
    replace 2 with (2^ Z.of_N 1) by reflexivity. rewrite <- Z_land_ones'. simpl. cbv [Z.ones]; simpl.
    replace 1 with (2^0) by reflexivity. rewrite Z.land_pow2_testbit.

 
    Search Z.shiftr. replace 2 with (2^ Z.of_N 1) by reflexivity.
    rewrite <- Z_land_ones'. replace (Z.ones (Z.of_N 1)) with (Z.shiftr (Z.ones (Z.of_N (s + 1))) (Z.of_N s)).
    + rewrite <- Z.shiftr_land. Search (_ * _ ^ _). rewrite <- Z.pow_succ_r in E by lia. simpl in E.
      Search (Z.succ (Z.of_N _)). rewrite <- N2Z.inj_succ in E. Check Z.mod_small.
      assert ((y1' + y2') mod 2 ^ Z.of_N (s + 1) = (y1' + y2')).
      2: { rewrite <- H0. rewrite <- Z_land_ones'. (Z.of_N simpl. rewrite Z.shiftr_div_pow2 by lia. Search Z.modulo. Search Z.shiftr. subst. Check Z.mod_small.
    (*   *)Check Z.land_ones. Check Z.shiftr_land. rewrite Z.land_ones by lia.
    apply Z.mod_small.

 apply eval_list_of_addends with (f := f) in H1.
  apply eval_list_of_addends with (f := f) in H2.
  Check eval_eval. apply (eval_eval _ _ _ _ H3) in H1. apply (eval_eval _ _ _ _ H2) in H4.
  subst. rewrite Z.add_0_r. inv H3. clear H1. inv H2. clear H1. Check small_sum. apply small_sum in H5.
  apply small_sum in H4. repeat rewrite Z.shiftr_div_pow2; try lia. Search (_ + _ <= _ + _)%Z.
  destruct H5 as [H5' H5]. destruct H4 as [H4' H4]. Check Z.add_le_mono. apply (Z.add_le_mono _ _ _ _ H5) in H4.
  cbv [Z.ones] in H4. repeat rewrite Z.shiftl_1_l in H4. assert (E : y1 + y0 < 2 * (2 ^ Z.of_N s)) by lia.
  Check Z.div_lt_upper_bound. assert ((y1 + y0) / 2 ^ Z.of_N s < 2).
  - apply Z.div_lt_upper_bound; lia.
  - apply (Z.add_le_mono _ _ _ _ H5') in H4'. Check Z.mod_small.
    symmetry. apply Z.mod_small. split.
    + Search Z.div. apply Z.div_pos.
      -- apply H4'.
      -- lia.
    + apply H. *)

Definition exprs_of_carries (s : OperationSize) (carries : list (list (list idx))) : list expr :=
  map (expr_of_a_carry s) carries.

(* Definition value_of_a_carry (val : idx -> Z) (s : OperationSize) (carry : list (list idx)) : Z :=
  let sums := map (fun addends => keep s (fold_right (fun x y => Z.add (val x) y) 0%Z addends)) carry in
  Z.shiftr (fold_right Z.add 0%Z sums) (Z.of_N s).

Definition value_of_carries (val : idx -> Z) (s : OperationSize) (carries : list (list (list idx))) : Z :=
  let values := map (value_of_a_carry val s) carries in
  fold_right Z.add 0%Z values. *)

Search eval.

Lemma eval_withadc_without' (ctx : symbol -> option Z) (d : dag) (s : OperationSize):
  forall args n,
  let (withadc, without) := withadc_without d s args in
  eval ctx d (ExprApp (add s, map ExprRef args)) n ->
  eval ctx d (ExprApp (add s, map ExprRef without ++ exprs_of_carries s withadc)) n.
Proof.
  intros args. induction args as [| i args'].
  - simpl. intros. apply H.
  - destruct (withadc_without d s (i :: args')) as [withadc without] eqn:E. simpl in E.
    destruct (withadc_without d s args') as [withadc' without'] eqn:E1.
    intros.
    assert (Lemma: (withadc, without) = (withadc', i :: without') -> 
                   eval ctx d (ExprApp (add s, map ExprRef without ++ exprs_of_carries s withadc)) n).
    { clear E. intros E. injection E as E E'. rewrite E in *. rewrite E' in *. clear E E'.
      
      rewrite app_is_cons in H. rewrite map_app in H. apply break_add_backwards in H.
      destruct H as [n_0 [n_1 [H2 [H3 H4] ] ] ]. simpl in H2. injection H2 as H2. subst.
      apply IHargs' in H4. clear IHargs'.

      simpl. rewrite app_is_cons. apply break_add with (m1 := n_0) (m2 := n_1).
      - simpl. reflexivity.
      - assumption.
      - assumption.
    }
    destruct (dag.lookup d i) as [ [op op_args]|] eqn:E_dlook.
    + destruct op_args as [| arg1 [| arg2 [| arg3 op_args'] ] ] eqn:E_op_args.
      -- apply Lemma. rewrite <- E. destruct op; reflexivity.
      -- apply Lemma. rewrite <- E. destruct op; reflexivity.
      -- destruct op; try (apply Lemma; rewrite <- E; reflexivity).
         destruct (s0 =? s)%N eqn:Es; destruct (is_bounded_by d (2 ^ Z.of_N s - 1) arg1) eqn:Eb1;
         destruct (is_bounded_by d (2 ^ Z.of_N s - 1) arg2) eqn:Eb2; try (apply Lemma; rewrite <- E; reflexivity).
         clear Lemma. simpl in E. injection E as E E_. apply N.eqb_eq in Es. subst.
         simpl in H. rewrite app_is_cons in H. apply break_add_backwards in H.
         destruct H as [n_0 [n_1 [H1 [H2 H3] ] ] ]. apply IHargs' in H3. clear IHargs'.
         apply break_add_backwards in H3. destruct H3 as [n_1_0 [n_1_1 [H3 [H4 H5] ] ] ].
         injection H1 as H1; subst. injection H3 as H3; subst.
         apply break_add with (m1 := n_1_0) (m2 := Z.land (n_0 + (n_1_1 + 0)) (Z.ones (Z.of_N s))).
         ++ simpl. f_equal. repeat rewrite Z.add_0_r. repeat rewrite Z_land_ones'.
            Search ((_ + (_ mod _)) mod _). repeat rewrite <- PullPush.Z.add_mod_r. f_equal. lia.
         ++ apply H4.
         ++ simpl. rewrite app_is_cons. apply break_add with (m1 := n_0) (m2 := n_1_1).
           --- simpl. f_equal.
           --- inv H2. inv H1. inv H7. injection H6 as H6; subst. Check eval_expr_of_a_carry''.
               Check collapse_op. apply (collapse_op _ _ _ _ _ _ H2) in E_dlook. clear H2.
               apply EApp with (args' := [y]).
              +++ constructor.
                ---- apply eval_expr_of_a_carry''; assumption.
                ---- constructor.
              +++ simpl. reflexivity.
           --- assumption.
      -- apply Lemma. rewrite <- E. destruct op; reflexivity.
    + apply Lemma. rewrite E. reflexivity.
Qed.

Lemma evalZ_withadc_without (ctx : symbol -> option Z) (d : dag) (s : OperationSize):
  forall args n,
  let (withadc, without) := withadc_without d s args in
  eval ctx d (ExprApp (addZ, map ExprRef args)) n ->
  eval ctx d (ExprApp (addZ, map ExprRef without ++ exprs_of_carries s withadc)) n.
Proof.
  intros args. induction args as [| i args'].
  - simpl. intros. apply H.
  - destruct (withadc_without d s (i :: args')) as [withadc without] eqn:E. simpl in E.
    destruct (withadc_without d s args') as [withadc' without'] eqn:E1.
    intros.
    assert (Lemma: (withadc, without) = (withadc', i :: without') -> 
                   eval ctx d (ExprApp (addZ, map ExprRef without ++ exprs_of_carries s withadc)) n).
    { clear E. intros E. injection E as E E'. rewrite E in *. rewrite E' in *. clear E E'.
      
      rewrite app_is_cons in H. rewrite map_app in H. apply break_addZ_backwards in H.
      destruct H as [n_0 [n_1 [H2 [H3 H4] ] ] ]. simpl in H2. injection H2 as H2. subst.
      apply IHargs' in H4. clear IHargs'.

      simpl. rewrite app_is_cons. apply break_addZ with (m1 := n_0) (m2 := n_1).
      - simpl. reflexivity.
      - assumption.
      - assumption.
    }
    destruct (dag.lookup d i) as [ [op op_args]|] eqn:E_dlook.
    + destruct op_args as [| arg1 [| arg2 [| arg3 op_args'] ] ] eqn:E_op_args.
      -- apply Lemma. rewrite <- E. destruct op; reflexivity.
      -- apply Lemma. rewrite <- E. destruct op; reflexivity.
      -- destruct op; try (apply Lemma; rewrite <- E; reflexivity).
         destruct (s0 =? s)%N eqn:Es; destruct (is_bounded_by d (2 ^ Z.of_N s - 1) arg1) eqn:Eb1;
         destruct (is_bounded_by d (2 ^ Z.of_N s - 1) arg2) eqn:Eb2; try (apply Lemma; rewrite <- E; reflexivity).
         clear Lemma. simpl in E. injection E as E E_. apply N.eqb_eq in Es. subst.
         simpl in H. rewrite app_is_cons in H. apply break_addZ_backwards in H.
         destruct H as [n_0 [n_1 [H1 [H2 H3] ] ] ]. apply IHargs' in H3. clear IHargs'.
         apply break_addZ_backwards in H3. destruct H3 as [n_1_0 [n_1_1 [H3 [H4 H5] ] ] ].
         injection H1 as H1; subst. injection H3 as H3; subst.
         apply break_addZ with (m1 := n_1_0) (m2 := n_0 + n_1_1 + 0).
         ++ simpl. f_equal. lia.
         ++ apply H4.
         ++ simpl. rewrite app_is_cons. apply break_addZ with (m1 := n_0) (m2 := n_1_1).
           --- simpl. f_equal. lia.
           --- inv H2. inv H1. inv H7. injection H6 as H6; subst. Check eval_expr_of_a_carry''.
               Check collapse_op. apply (collapse_op _ _ _ _ _ _ H2) in E_dlook. clear H2.
               apply EApp with (args' := [y]).
              +++ constructor.
                ---- apply eval_expr_of_a_carry''; assumption.
                ---- constructor.
              +++ simpl. reflexivity.
           --- assumption.
      -- apply Lemma. rewrite <- E. destruct op; reflexivity.
    + apply Lemma. rewrite E. reflexivity.
Qed.

(*          simpl. rewrite app_is_cons. apply break_add in H1.
         destruct H1 as [a2_0 [a2_1 [H1 [H2 H3] ] ] ]. rewrite app_is_cons in H. rewrite map_app in H.
         apply break_add_backwards in H. destruct H as [n_0 [n_1 [H4 [H5 H6] ] ] ].
         apply (IHargs' _ _ _ H6 H0) in H3. clear H6 H0 IHargs'.
         inv H4. inv H1. inv H3. (* now must just show that a2_0 = n_0 *) Check eval_expr_of_a_carry'.
         inv H5. inv H1. inv H6. inv H3. inv H4. rewrite H0 in E_dlook. inv E_dlook. clear H0 E1. inv H5.
           Check collapse_op. 

         apply (eval_expr_of_a_carry' ctx d s (N.to_nat (dag.size d)) arg1 arg2 a2_0 n_0 Eb1 Eb2 .
         assert (E : a2_0 = n_0). 
         ++ apply (eval_expr_of_a_carry' ctx d s (N.to_nat (dag.size d)) arg1 arg2 a2_0 n_0). 
            --- assumption. 
            --- assumption.
            --- assumption. try assumption.
          : { simpl. Admitted. *)

(* Lemma eval_withadc_without (ctx : symbol -> option Z) (d : dag) (s : OperationSize):
  forall args n a1 a2,
  let (withadc, without) := withadc_without d s args in
  eval ctx d (ExprApp (add s, map ExprRef args)) n ->
  eval ctx d (ExprApp (add s, map ExprRef without)) a1 ->
  eval ctx d (ExprApp (add s, exprs_of_carries s withadc)) a2 ->
  interp_op (fun _ => None) (add s) [a1; a2] = Some n.
Proof.
  intros args. induction args as [| i args'].
  - simpl. intros.
    inv H. inv H4. inv H6. inv H0. inv H3. inv H5. inv H1. inv H2. inv H4.
    reflexivity.
  - destruct (withadc_without d s (i :: args')) as [withadc without] eqn:E. simpl in E.
    destruct (withadc_without d s args') as [withadc' without'] eqn:E1.
    intros.
    assert (Lemma: (withadc, without) = (withadc', i :: without') -> interp_op (fun _=>None) (add s) [a1; a2] = Some n).
    { clear E. intros E. injection E as E E'. rewrite E in *. rewrite E' in *. clear E E'.
      
      rewrite app_is_cons in H. rewrite map_app in H. apply break_add_backwards in H.
      destruct H as [n_0 [n_1 [H2 [H3 H4] ] ] ]. simpl in H2. injection H2 as H2. subst.

      rewrite app_is_cons in H0. rewrite map_app in H0. apply break_add_backwards in H0.
      destruct H0 as [a1_0 [a1_1 [H5 [H6 H7] ] ] ]. simpl in H5. injection H5 as H5. subst.
      
      simpl. repeat rewrite Z_land_ones'. repeat rewrite Z.add_0_r. f_equal.
      rewrite <- PullPush.Z.add_mod_l. Check eval_eval. apply (eval_eval _ _ _ _ H3) in H6. clear H3. subst.
      apply (IHargs' _ _ _ H4 H7) in H1. clear H4 H7. rewrite <- Z.add_assoc. rewrite PullPush.Z.add_mod_full.
      symmetry. rewrite PullPush.Z.add_mod_full. f_equal. f_equal. simpl in H1. injection H1 as H1.
      rewrite Z_land_ones' in H1. rewrite Z.add_0_r in H1. subst. rewrite Zmod_mod. reflexivity.
    }
    destruct (dag.lookup d i) as [ [op op_args]|] eqn:E_dlook.
    + destruct op_args as [| arg1 [| arg2 [| arg3 op_args'] ] ] eqn:E_op_args.
      -- apply Lemma. rewrite <- E. destruct op; reflexivity.
      -- apply Lemma. rewrite <- E. destruct op; reflexivity.
      -- destruct op; try (apply Lemma; rewrite <- E; reflexivity).
         destruct (s0 =? s)%N eqn:Es; destruct (is_bounded_by d (2 ^ Z.of_N s - 1) arg1) eqn:Eb1;
         destruct (is_bounded_by d (2 ^ Z.of_N s - 1) arg2) eqn:Eb2; try (apply Lemma; rewrite <- E; reflexivity).
         clear Lemma. simpl in E. injection E as E E_. subst.
         simpl in H1. rewrite app_is_cons in H1. apply break_add_backwards in H1.
         destruct H1 as [a2_0 [a2_1 [H1 [H2 H3] ] ] ]. rewrite app_is_cons in H. rewrite map_app in H.
         apply break_add_backwards in H. destruct H as [n_0 [n_1 [H4 [H5 H6] ] ] ].
         apply (IHargs' _ _ _ H6 H0) in H3. clear H6 H0 IHargs'.
         inv H4. inv H1. inv H3. (* now must just show that a2_0 = n_0 *) Check eval_expr_of_a_carry'.
         inv H5. inv H1. inv H6. inv H3. inv H4. rewrite H0 in E_dlook. inv E_dlook. clear H0 E1. inv H5.
           Check collapse_op. 

         apply (eval_expr_of_a_carry' ctx d s (N.to_nat (dag.size d)) arg1 arg2 a2_0 n_0 Eb1 Eb2 .
         assert (E : a2_0 = n_0). 
         ++ apply (eval_expr_of_a_carry' ctx d s (N.to_nat (dag.size d)) arg1 arg2 a2_0 n_0). 
            --- assumption. 
            --- assumption.
            --- assumption. try assumption.
          : { simpl. Admitted. *)

(* Lemma collapse_addition' : 

Check eval_expr_of_a_carry. Check collapse_addition.
            apply eval_list_of_addends with (f := (N.to_nat (dag.size d))) in H5.
            cbv-
 *)

Local Open Scope nat_scope.
(* 
  destruct (withadc_without d s args) as [withadc without] eqn:E1.
  intros. *)

Require Import Coq.Sorting.Mergesort.

Module listAddendListOrder <: TotalLeBool.
  Definition t : Type := list (list idx).
  Fixpoint total_length {X} (l : list (list X)) : nat :=
    match l with
    | [] => O
    | x :: l' => length x + total_length l'
    end.
  Definition leb (x y : t) : bool :=
    total_length x <=? total_length y.
  Infix "<=?" := leb (at level 70, no associativity).
  Theorem leb_total : forall x y, x <=? y = true \/ y <=? x = true.
  Proof. intros. unfold leb. repeat rewrite Nat.leb_le. lia. Qed.
End listAddendListOrder.
Module Import listAddendListSort := Sort listAddendListOrder.

Print sort.
Print N.sort.
Print merge.
Print N.
Print N.Sort.merge.

(* Fixpoint eqb (l1 l2 : list idx) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: l1', x2 :: l2' => N.eqb x1 x2 && eqb l1' l2'
  | _, _ => false
  end. *)

(* Fixpoint merge_list (l : list (list idx)) : list idx := (* horribly inefficient *)
  match l with
  | [] => []
  | x :: l' => N.Sort.merge x (merge_list l')
  end. *)

Definition merge_list (l : list (list idx)) : list idx :=
  let l' := fold_right (@app idx) [] l in
  N.sort l'.

(* for example, insert_small [[6], [7]] [[[6, 7], [8]], ...] => [[[6], [7], [8]], ...] *)
Fixpoint insert_small (small : list (list idx)) (big : list (list idx)) (* : option (list (list idx)) *) :=
  let small_all := merge_list small in
  match big with
  | [] => None
  | maybe_small :: big' =>
    if (list_beq N (N.eqb) maybe_small (merge_list small))
    then
      Some (small ++ big')
    else
      match insert_small small big' with
      | Some new_big' => Some (maybe_small :: new_big')
      | None => None
      end
  end.

Lemma lists_equal (l1 l2 : list N) :
  l1 = l2 <->
  list_beq N N.eqb l1 l2 = true.
Proof.
  intros. apply Bool.reflect_iff. apply reflect_eq_list.
Qed.

Check expr_of_a_carry.

Check break_addZ.

Local Open Scope Z_scope.

Lemma break_expr_of_a_carry ctx d s l1 l2 n1 n2 n:
  interp_op (fun _ : symbol => None) addZ [n1; n2] = Some n ->
  eval ctx d (expr_of_a_carry s l1) n1 ->
  eval ctx d (expr_of_a_carry s l2) n2 ->
  eval ctx d (expr_of_a_carry s (l1 ++ l2)) n.
Proof.
  intros. cbv [expr_of_a_carry] in *.
  inv H0. inv H4. inv H7. inv H8. inv H4. inv H5. inv H8. inv H6.
  inv H1. inv H4. inv H7. inv H8. inv H4. inv H5. inv H8. inv H6.
  apply EApp with (args' := [y + y0; Z.of_N s]).
  - constructor.
    + rewrite map_app. apply break_addZ with (m1 := y) (m2 := y0).
      -- simpl. f_equal. lia.
      -- assumption.
      -- assumption.
    + constructor.
      -- apply EApp with (args' := []).
        ++ constructor.
        ++ simpl. reflexivity.
      -- constructor.
  - rewrite <- H. clear H H2 H3. simpl. f_equal. Abort. (* NOT true *)

Lemma break_expr_of_a_carry' ctx d s l1 l2 n1 n2 :
  eval ctx d (expr_of_a_carry s l1) n1 ->
  eval ctx d (expr_of_a_carry s l2) n2 ->
  exists m1 m2,
  n1 = m1 / 2 ^ Z.of_N s /\
  n2 = m2 / 2 ^ Z.of_N s /\
  eval ctx d (expr_of_a_carry s (l1 ++ l2)) ((m1 + m2) / 2 ^ Z.of_N s).
Proof.
  intros.
  inv H. inv H3. inv H6. inv H7.
  inv H3. inv H4. inv H7. rename y into m1.
  inv H0. inv H3. inv H7. inv H8.
  inv H3. inv H4. inv H8. inv H6. inv H5. rename y into m2.
  exists m1. exists m2. split.
  - rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  - split.
    + rewrite Z.shiftr_div_pow2 by lia. reflexivity.
    + cbv [expr_of_a_carry]. apply EApp with (args' := [m1 + m2; Z.of_N s]).
      -- constructor.
        ++ rewrite map_app. apply break_addZ with (m1 := m1) (m2 := m2).
          --- simpl. f_equal. lia.
          --- assumption.
          --- assumption.
        ++ constructor.
          --- apply EApp with (args' := []).
            +++ constructor.
            +++ reflexivity.
          --- constructor.
      -- simpl. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma break_expr_of_a_carry_backwards ctx d s l1 l2 n:
  eval ctx d (expr_of_a_carry s (l1 ++ l2)) n ->
  exists m1 m2,
  n = (m1 + m2) / 2 ^ Z.of_N s /\
  eval ctx d (expr_of_a_carry s l1) (m1 / 2 ^ Z.of_N s) /\
  eval ctx d (expr_of_a_carry s l2) (m2 / 2 ^ Z.of_N s).
Proof. Admitted.

Lemma permute_commutative G op args n : commutative op = true ->
  interp_op G op args = Some n ->
  forall args', Permutation.Permutation args args' ->
  interp_op G op args' = Some n.
Proof using Type.
  destruct op; inversion 1; cbn; intros ? ? Hp;
    try (erewrite <- Z.fold_right_Proper_Permutation_add; eauto);
    try (erewrite <- Z.fold_right_Proper_Permutation_mul; eauto);
    try (erewrite <- Z.fold_right_Proper_Permutation_land; eauto);
    try (erewrite <- Z.fold_right_Proper_Permutation_lor; eauto);
    try (erewrite <- Z.fold_right_Proper_Permutation_lxor; eauto).
  { erewrite <-(Z.fold_right_Proper_Permutation_add _ _ eq_refl _ (map _ args'));
      eauto using Permutation.Permutation_map. }
Qed.

Lemma eval_commutative ctx d o args1 args2 n :
  commutative o = true ->
  Permutation.Permutation args1 args2 ->
  eval ctx d (ExprApp (o, args1)) n ->
  eval ctx d (ExprApp (o, args2)) n.
Proof.
  intros. inv H1. Check Permutation_Forall2. apply (Permutation_Forall2 H0) in H4.
  destruct H4 as [args2' [H4 H5] ]. apply EApp with (args' := args2').
  - assumption.
  - apply permute_commutative with (args := args'); assumption.
Qed.

Lemma eval_merge_list ctx d s small n : 
  eval ctx d (ExprApp (addZ, map (fun addends : list idx => ExprApp (add s, map ExprRef addends)) small)) n ->
  eval ctx d (ExprApp (add s, map ExprRef (merge_list small))) (n mod 2 ^ Z.of_N s).
Proof.
  intros. cbv [merge_list]. apply eval_commutative with (args1 := map ExprRef (fold_right (app (A:=idx)) [] small)).
  - reflexivity.
  - apply Permutation_map. Search N.sort. apply N.Sort.Permuted_sort.
  - generalize dependent n. induction small as [| first small' IHsmall']. 
    + simpl. intros. apply EApp with (args' := []).
      -- constructor.
      -- inv H. inv H2. inv H4. reflexivity.
    + intros. simpl in H. rewrite app_is_cons in H. apply break_addZ_backwards in H. destruct H as [n1 [n2 [H1 [H2 H3] ] ] ].
      apply IHsmall' in H3. clear IHsmall'. 
      inv H2. inv H4. inv H7. inv H6. inv H1. repeat rewrite Z.add_0_r.
      simpl. rewrite map_app. apply break_add with (m1 := y) (m2 := n2 mod 2 ^ Z.of_N s).
      -- simpl. rewrite Z_land_ones'. f_equal. rewrite Z.add_0_r. Search ((_ + _ mod _) mod _). apply Zplus_mod_idemp_r.
      -- apply H2.
      -- apply H3.
Qed.

(* H3 : eval ctx d (ExprApp (addZ, [ExprApp (add s, map ExprRef (merge_list small))])) sm_mod_d
 *)

Lemma mod_unchanged ctx d s small :
  forall big new_big n m,
  insert_small small big = Some new_big ->
  eval ctx d (ExprApp (addZ, map (fun addends : list idx => ExprApp (add s, map ExprRef addends)) big)) n ->
  eval ctx d (ExprApp (addZ, map (fun addends : list idx => ExprApp (add s, map ExprRef addends)) new_big)) m ->
  n mod 2 ^ Z.of_N s = m mod 2 ^ Z.of_N s.
Proof.
  intros big. induction big as [| maybe_small big' IHbig'].
  - intros. simpl in H. discriminate H.
  - intros. simpl in H.
    rewrite app_is_cons in H0.
    rewrite map_app in H0. apply break_addZ_backwards in H0. destruct H0 as [n1 [n2 [H2 [H3 H4] ] ] ].
     inv H2. simpl in H3.
    destruct (list_beq N N.eqb maybe_small (merge_list small)) eqn:E.
    + clear IHbig'. Check eval_merge_list. rewrite <- lists_equal in E. subst. inv H. 
      rewrite map_app in H1. apply break_addZ_backwards in H1. destruct H1 as [m1 [m2 [H5 [H6 H7] ] ] ].
      inv H5. apply eval_merge_list in H6. simpl in H3. inv H3. inv H1. inv H8. inv H5. rename y into n1.
      Check eval_eval. apply (eval_eval _ _ _ _ H2) in H6. clear H2. subst. apply (eval_eval _ _ _ _ H4) in H7. 
      clear H4. subst. repeat rewrite Z.add_0_r. Search ((_ mod _ + _) mod _). rewrite Zplus_mod_idemp_l. reflexivity.
    + clear E. destruct (insert_small small big') as [new_big'|].
      -- inv H.
         rewrite app_is_cons in H1. rewrite map_app in H1. apply break_addZ_backwards in H1.
         destruct H1 as [m1 [m2 [H5 [H6 H7] ] ] ]. simpl in H6. assert (H: n2 mod 2 ^ Z.of_N s = m2 mod 2 ^ Z.of_N s).
         ++ apply IHbig' with (new_big := new_big').
           --- reflexivity.
           --- assumption.
           --- assumption.
         ++ clear H4 H7 IHbig'. inv H5. apply (eval_eval _ _ _ _ H3) in H6. clear H3. subst.
            repeat rewrite Z.add_0_r. Search (((_ mod _) + (_ mod _)) mod _). rewrite Zplus_mod.
            rewrite H. rewrite <- Zplus_mod. reflexivity.
      -- discriminate H.
Qed.

Lemma eval_insert_small' ctx d s :
  forall small big n1 n2 new_big,
  eval ctx d (expr_of_a_carry s small) n1 ->
  eval ctx d (expr_of_a_carry s big) n2 ->
  insert_small small big = Some new_big ->
  eval ctx d (expr_of_a_carry s new_big) (n1 + n2).
Proof.
  intros small big. generalize dependent small.
  induction big as [| maybe_small big' IHbig'].
  - simpl. intros. discriminate H1.
  - intros. simpl in H1. destruct (list_beq N N.eqb maybe_small (merge_list small)) eqn:E.
    + rewrite <- lists_equal in E. subst. injection H1 as H1. subst. clear IHbig'.
      inv H. inv H3. inv H6. inv H7.
      inv H3. inv H5. inv H4. inv H7.
      inv H0. inv H3. inv H6. inv H7. inv H3. inv H4. inv H7. inv H5.
      rewrite app_is_cons in H1. apply break_addZ_backwards in H1.
      destruct H1 as [sm_mod_d [big_sum [H3 [H4 H5] ] ] ]. rename y into small_sum. inv H3.
      cbv [expr_of_a_carry]. repeat rewrite Z.add_0_r. apply EApp with (args' := [small_sum + big_sum; Z.of_N s]).
        ++ constructor.
          --- rewrite map_app. apply break_addZ with (m1 := small_sum) (m2 := big_sum).
            +++ simpl. f_equal. lia.
            +++ assumption.
            +++ assumption.
          --- constructor.
            +++ eapply EApp; auto.
            +++ constructor.
        ++ inv H4. inv H1. inv H7. inv H6. apply eval_merge_list in H2. Check eval_eval.
           apply (eval_eval _ _ _ _ H2) in H3. clear H2. subst.
           simpl. f_equal. repeat rewrite Z.shiftr_div_pow2 by lia. rewrite Z.add_0_r. Search ((_ + _) / _).
           rewrite Div.Z.div_add_mod_cond_l by lia. lia.
    + destruct (insert_small small big') as [new_big' |] eqn:E'.
      -- (* n1 = small_sum / d; n2 = (big_sum + small_sum mod d) / d; n1 + n2 = (small_sum + big_sum) / d. *) clear E. inv H0. inv H4. inv H7. inv H8. inv H4. inv H5. inv H8.  simpl. inv H1. 
         rewrite app_is_cons in H3. apply break_addZ_backwards in H3.
         destruct H3 as [maybe_small_sum [big'_sum [H1 [H2 H3] ] ] ]. inv H1. inv H6.
         assert (eval ctx d (expr_of_a_carry s big') (Z.shiftr (big'_sum) (Z.of_N s))).
         {  cbv [expr_of_a_carry]. apply EApp with (args' := [big'_sum; Z.of_N s]).
            - constructor.
              + assumption.
              + constructor.
                -- apply EApp with (args' := []).
                  ++ constructor.
                  ++ reflexivity.
                -- constructor.
            - reflexivity. }
          remember (IHbig' _ _ _ _ H H0 E') as E''. clear HeqE'' H H0 IHbig'. rewrite Z.add_0_r.
          cbv [expr_of_a_carry]. cbv [expr_of_a_carry] in E'.
          inv E''. inv H5. inv H1. inv H7. inv H8. inv H4. inv H6. inv H8. rename y into new_big'_sum.
          apply EApp with (args' := [maybe_small_sum + new_big'_sum; Z.of_N s]).
          ++ constructor.
            --- rewrite app_is_cons. rewrite map_app. apply break_addZ with (m1 := maybe_small_sum) (m2 := new_big'_sum).
                +++ simpl. f_equal. lia.
                +++ simpl. assumption.
                +++ assumption.
            --- constructor.  (* ((x + y, z); (x, y)) -> ((x, y, z))
                              expr_of_a_carry (x + y, z) + expr_of_a_carry (x, y) = expr_of_a_carry (x, y, z) *)

              +++ apply EApp with (args' := []).
                ---- constructor.
                ---- reflexivity.
              +++ constructor.
          ++ simpl. f_equal. simpl in H0. injection H0 as H0. Check mod_unchanged.
             apply (mod_unchanged _ _ _ _ _ _ _ _ E' H3) in H5. clear H2 H3 E'.
             repeat rewrite Z.shiftr_div_pow2 in * by lia. rewrite Div.Z.div_add_mod_cond_r by lia. rewrite H0.
             rewrite <- H5. rewrite (Z.add_comm n1). rewrite Z.add_assoc. rewrite <- Div.Z.div_add_mod_cond_r by lia.
             lia.
      -- discriminate H1.
Qed.

(* repeat rewrite Z.shiftr_div_pow2 in * by lia.
             Check Div.Z.div_add_mod_cond_l. rewrite Div.Z.div_add_mod_con2d_r by lia. rewrite H5.
             rewrite (Z.add_comm n1). rewrite Z.add_assoc. repeat rewrite (Div.Z.div_add_mod_cond_l maybe_small_sum) by lia.
             replace (maybe_small_sum / 2 ^ Z.of_N s) with 0.
             {  

 rewrite H5. repeat rewrite Z.shiftr_div_pow2 by lia. simpl in 



eval ctx d (expr_of_a_carry s (a :: l)) n *)


(* Lemma eval_insert_small ctx d s :
  forall small big n new_big,
  eval ctx d (ExprApp (addZ, exprs_of_carries s [small; big])) n ->
  insert_small small big = Some new_big ->
  eval ctx d (ExprApp (addZ, exprs_of_carries s [new_big])) n.
Proof.
  intros small big. generalize dependent small.
  induction big as [| maybe_small big' IHbig'].
  - simpl. intros. discriminate H0.
  - intros. simpl in H0. destruct (list_beq N N.eqb maybe_small (merge_list small)) eqn:E.
    + rewrite <- lists_equal in E. subst. injection H0 as H0. subst. clear IHbig'.
      simpl in *. apply EApp with (args' := [n]).
      -- constructor; try constructor.
         inv H. inv H2. inv H5. inv H6.
         inv H1. inv H3. inv H7. inv H8.
         inv H3. inv H5. inv H8. inv H6.
         inv H2. inv H3. inv H7. inv H8.
         inv H3. inv H5. inv H8. inv H6. inv H4.
         rewrite app_is_cons in H2. apply break_addZ_backwards in H2.
         destruct H2 as [sm_mod_d [big_sum [H2 [H3 H4] ] ] ]. rename y1 into small_sum. inv H2.
         cbv [expr_of_a_carry]. repeat rewrite Z.add_0_r. apply EApp with (args' := [small_sum + big_sum; Z.of_N s]).
        ++ constructor.
          --- rewrite map_app. apply break_addZ with (m1 := small_sum) (m2 := big_sum).
            +++ simpl. f_equal. lia.
            +++ assumption.
            +++ assumption.
          --- constructor.
            +++ eapply EApp; auto.
            +++ constructor.
        ++ inv H3. inv H2. inv H7. inv H6. apply eval_merge_list in H1. Check eval_eval.
           apply (eval_eval _ _ _ _ H1) in H3. clear H1. subst.
           simpl. f_equal. repeat rewrite Z.shiftr_div_pow2 by lia. rewrite Z.add_0_r. Search ((_ + _) / _).
           rewrite Div.Z.div_add_mod_cond_l by lia. lia.
      -- simpl. f_equal. lia.
    + destruct (insert_small small big') as [new_big' |] eqn:E'.
      -- inv H0. simpl. cbv [expr_of_a_carry]. pply H.
      --  *)


(* (y + y1) / 2^s = 

eoc big' -> y_2 / 2^s
eoc small -> y1 / 2^s 
y_1 = y1 mod 2^s
y mod 2

(small + big) / d = (small mod d + big mod d) / d + small / d + big / d
y = small / d
y0 = (small mod d + big') / d

y_1 = small mod d
y_2 = big 
y1 = small *)


Compute (insert_small [ [09]; [18] ] [ [27]; [09; 18] ])%N.

Print dag.t.

(* returns Some (big, l - big) if there exists a big in l that small can be inserted into.  else, returns None *)
Fixpoint big_merged_thing (small : list (list idx)) (l : list (list (list idx))) : option ((list (list idx)) * list (list (list idx))) :=
  match l with
  | [] => None
  | maybe_big :: l' =>
    match insert_small small maybe_big with
    | Some big_thing => Some (big_thing, l')
    | None =>
      match big_merged_thing small l' with
      | Some (big_thing, l'') =>
        Some (big_thing, maybe_big :: l'')
      | None => None
      end
    end
  end.

Lemma eval_big_merged_thing ctx d s small :
  forall carries big_thing remaining n1 n2,
  eval ctx d (expr_of_a_carry s small) n1 ->
  eval ctx d (ExprApp (addZ, exprs_of_carries s carries)) n2 ->
  big_merged_thing small carries = Some (big_thing, remaining) ->
  eval ctx d (ExprApp (addZ, exprs_of_carries s (big_thing :: remaining))) (n1 + n2).
Proof.
  intros carries. induction carries as [| carry carries' IHcarries'].
  - intros. simpl in H1. discriminate H1.
  - intros. simpl in H1. destruct (insert_small small carry) as [big_thing'|] eqn:E.
    + inv H1. clear IHcarries'. Check eval_insert_small'.
      simpl in H0. rewrite app_is_cons in H0. apply break_addZ_backwards in H0. destruct H0 as [n2_1 [n2_2 [H1 [H2 H3] ] ] ].
      inv H1. inv H2. inv H4. inv H7. inv H6. Check eval_insert_small'. apply (eval_insert_small' _ _ _ _ _ _ _ _ H H2) in E.
      simpl. rewrite app_is_cons. apply break_addZ with (m1 := n1 + y) (m2 := n2_2).
      -- simpl. repeat rewrite Z.add_0_r. f_equal. lia.
      -- apply EApp with (args' := [n1 + y]).
        ++ constructor.
          --- assumption.
          --- constructor.
        ++ simpl. f_equal. lia.
      -- assumption.
    + destruct (big_merged_thing small carries') as [ [big_thing_ l'']|] eqn:E'.
      -- inv H1. clear E. simpl in H0. rewrite app_is_cons in H0. apply break_addZ_backwards in H0.
         destruct H0 as [n2_1 [n2_2 [H1 [H2 H3] ] ] ].
         assert (Some (big_thing, l'') = Some (big_thing, l'')) by reflexivity.
         apply (IHcarries' _ _ _ _ H H3) in H0. clear IHcarries' H H3. inv H1.
         simpl in H0. rewrite app_is_cons in H0. apply break_addZ_backwards in H0.
         destruct H0 as [m1 [m2 [H3 [H4 H5] ] ] ].
         simpl. rewrite app_is_cons. apply break_addZ with (m1 := m1) (m2 := m2 + n2_1).
        ++ simpl. f_equal. simpl in H3. injection H3 as H3. lia.
        ++ assumption.
        ++ rewrite app_is_cons. apply break_addZ with (m1 := n2_1) (m2 := m2).
          --- simpl. f_equal. lia.
          --- assumption.
          --- assumption.
      -- discriminate H1.
Qed.

(* assumes the list, and its elements, to be sorted *)
Fixpoint merge_carries_aux (l : list (list (list idx))) (len : nat) : list (list (list idx)) :=
  match len with
  | O => l
  | S len' =>
    match l with
    | [] => []
    | maybe_small :: l' =>
      match big_merged_thing maybe_small l' with
      | Some (big_thing, remaining) => merge_carries_aux (merge [big_thing] remaining) len'
      | None => maybe_small :: (merge_carries_aux l' len')
      end
    end
  end.

Lemma eval_merge_carries_aux ctx d s n withadc len:
  eval ctx d (ExprApp (addZ, exprs_of_carries s withadc)) n ->
  eval ctx d (ExprApp (addZ, exprs_of_carries s (merge_carries_aux withadc len))) n.
Proof.
  generalize dependent n. generalize dependent len. induction len as [| len'].
  - simpl. intros. apply H.
  - cbv [merge_carries_aux]. simpl. intros. Admitted.

Definition merge_carries (l : list (list (list idx))) : list (list (list idx)) :=
  let l := map (fun (a : list (list idx)) => (map (fun (b : list idx) => N.sort b) a)) l in
  let l := sort l in
  merge_carries_aux l (length l).

Lemma eval_merge_carries ctx d s n withadc:
  eval ctx d (ExprApp (addZ, exprs_of_carries s withadc)) n ->
  eval ctx d (ExprApp (addZ, exprs_of_carries s (merge_carries withadc))) n.
Proof. Admitted.


Compute (big_merged_thing [ [18]; [09] ] [ [ [27]; [09; 18] ] ])%N.
Compute (insert_small [ [09]; [18] ] [ [27]; [09; 18] ])%N. 

Compute ((merge_carries [ [ [27]; [18; 09] ]; [ [18]; [09] ]  ]%N)).

Print op.
Print expr.
Print merge_node.
Compute (dag.M idx).

Definition sum_idx {descr : description} (d : dag) (s : OperationSize) (indices : list idx) : idx * dag :=
  match indices with
  | [] => merge_node (add s, []) d (* should never happen *)
  | i :: [] => (i, d)
  | _ => merge_node (add s, indices) d
  end.

Print merge_node.

(* list of things to be added *)
Fixpoint split_carry_aux {descr : description} (d : dag) (s : OperationSize) (carry : list (list idx)) : list idx * dag :=
  match carry with
  | [] => ([], d)
  | _ :: [] => ([], d) (* should never happen *)
  | x :: more_stuff =>
    let (adc_arg_1, d1) := sum_idx d s x in
    let (adc_arg_2, d2) := sum_idx d1 s (fold_right (@app idx) [] more_stuff) in
    let (i, d3) := merge_node (addcarry s, [adc_arg_1; adc_arg_2]) d2 in
    let (is, d4) := split_carry_aux d3 s more_stuff in
    (i :: is, d4)
  end.

Module lexOrder <: TotalLeBool.
  Definition t : Type := list idx.
  Fixpoint leb (x y : t) : bool :=
    match x, y with
    | [], _ => true
    | x0 :: x', [] => false
    | x0 :: x', y0 :: y' => if N.eqb x0 y0 then leb x' y' else N.leb x0 y0
    end.
  Infix "<=?" := leb (at level 70, no associativity).
  Theorem leb_total : forall x y, x <=? y = true \/ y <=? x = true.
  Proof.
    intros x. induction x as [| x0 x' IHx'].
    - intros y. left. reflexivity.
    - intros y. destruct y as [|y0 y'].
      + right. reflexivity.
      + simpl. rewrite <- (N.eqb_sym x0 y0). destruct (x0 =? y0)%N. 
        -- apply IHx'.
        --  unfold leb. repeat rewrite N.leb_le. lia. Qed.
End lexOrder.
Module Import lexSort := Sort lexOrder.
Print sort.

(* merges the addcarries that make up the carry into the dag, returns a list of index references to the addcarries *)
Definition split_carry {descr : description} (d : dag) (s : OperationSize) (carry : list (list idx)) : list idx * dag :=
  let carry := map (fun x => N.sort x) carry in
  let carry := sort carry in
  split_carry_aux d s carry.

Fixpoint split_carries {descr : description} (d : dag) (s : OperationSize) (l : list (list (list idx))) : list idx * dag :=
  match l with
  | [] => ([], d)
  | carry :: more =>
    let (some_addends, d') := split_carry d s carry in
    let (more_addends, d'') := split_carries d' s more in
    (some_addends ++ more_addends, d'')
  end.

Definition standardize_adc_sum {descr : description} (d : dag) (idxs : list idx) (s : OperationSize) : list idx * dag :=
  let (withadc, without) := withadc_without d s idxs in
  let (standard_withadc, d') := split_carries d s (merge_carries withadc) in
  (standard_withadc ++ without, d').

Print dag.t.
Print description.

Definition d1 : dag := [(addcarry 64, [101; 102], None); (add 64, [101; 102], None); (addcarry 64, [1; 100], None)]%N.
Definition d2 : dag := [(addcarry 64, [101; 102], None); (add 64, [101; 102], None); (addcarry 64, [1; 103], None)]%N.
Definition d3 : dag := [(const 0, [], None); (const 1, [], None); (const 2, [], None); (const 3, [], None); (const 4, [], None); (const 5, [], None); (const 6, [], None); (const 7, [], None); (const 8, [], None); (add 64, [5; 7], None); (addcarry 64, [5; 7], None); (add 64, [0; 5; 7], None); (addcarry 64, [0; 9], None); (add 64, [0; 3; 5; 7], None); (addcarry 64, [3; 11], None); (addcarry 64, [1; 13], None)]%N.

Compute (standardize_adc_sum d3 [2; 4; 6; 8; 10; 12; 14; 15] 64)%N. (* this doesn't work *)

Compute (merge_carries (fst (withadc_without d3 64 [2; 4; 6; 8; 10; 12; 14; 15])))%N. (* because this doesn't work :) *)

Compute ((fst (withadc_without d3 64 [2; 4; 6; 8; 10; 12; 14; 15])))%N.

Print dag.lookup.
Compute (standardize_adc_sum d1 [0; 2] 64)%N.

Fixpoint merge {descr : description} (e : expr) (d : dag) : idx * dag :=
  match e with
  | ExprRef i => (i, d)
  | ExprApp (op, args) =>
    let idxs_d := List.foldmap merge args d in
    let idxs_d' := 
                if sum op (* yes, op can be add s *)
                then standardize_adc_sum (snd idxs_d) (fst idxs_d) 64%N (* FIXME: this 64 should not be hardcoded *)
                else idxs_d in
    let idxs := if commutative op
                then N.sort (fst idxs_d')
                else (fst idxs_d') in
    merge_node (op, idxs) (snd idxs_d')
  end.

Lemma node_beq_sound e x : node_beq N.eqb e x = true -> e = x.
Proof using Type.
  eapply Prod.internal_prod_dec_bl.
  { intros X Y; destruct (op_beq_spec X Y); congruence. }
  { intros X Y. eapply ListUtil.internal_list_dec_bl, N.eqb_eq. }
Qed.

Lemma eval_weaken_merge_node G d {dok : dag.ok d} {descr:description} x e n : eval G d e n -> eval G (snd (dag.merge_node x d)) e n.
Proof using Type.
  induction 1; subst; econstructor; eauto.
  { erewrite dag.lookup_merge_node by assumption.
    match goal with H : _ |- _ => rewrite H end; reflexivity. }
  all : eapply Forall2_weaken; [|eassumption].
  { intuition eauto. eapply H2. }
  { intuition eauto. eapply H1. }
Qed.

Lemma eval_weaken_symbols G1 G2 d e n
  (H : forall s v, G1 s = Some v -> G2 s = Some v)
  : eval G1 d e n -> eval G2 d e n.
Proof using Type.
  induction 1; subst; econstructor;
    intuition eauto using interp_op_weaken_symbols.
  { eapply Forall2_weaken; [|eassumption]; intros ? ? (?&?); eauto. }
  { eapply Forall2_weaken; [|eassumption]; intros ? ? (?&?); eauto. }
Qed.

Lemma eval_eval0 d e n G : eval (fun _ => None) d e n -> eval G d e n.
Proof using Type. eapply eval_weaken_symbols; congruence. Qed.

Lemma permute_commutative G op args n : commutative op = true ->
  interp_op G op args = Some n ->
  forall args', Permutation.Permutation args args' ->
  interp_op G op args' = Some n.
Proof using Type.
  destruct op; inversion 1; cbn; intros ? ? Hp;
    try (erewrite <- Z.fold_right_Proper_Permutation_add; eauto);
    try (erewrite <- Z.fold_right_Proper_Permutation_mul; eauto);
    try (erewrite <- Z.fold_right_Proper_Permutation_land; eauto);
    try (erewrite <- Z.fold_right_Proper_Permutation_lor; eauto);
    try (erewrite <- Z.fold_right_Proper_Permutation_lxor; eauto).
  { erewrite <-(Z.fold_right_Proper_Permutation_add _ _ eq_refl _ (map _ args'));
      eauto using Permutation.Permutation_map. }
Qed.

(* the gensym state cannot map anything past the end of the dag *)
Definition gensym_ok (G : symbol -> option Z) (d : dag) := forall s _v, G s = Some _v -> (s < dag.size d)%N.
Definition dag_ok G (d : dag) := dag.ok d /\ dag.all_nodes_ok d /\ forall i r, dag.lookup d i = Some r -> exists v, eval G d (ExprRef i) v.
Definition gensym_dag_ok G d := gensym_ok G d /\ dag_ok G d.

Lemma gensym_ok_size_Proper G d1 d2
      (H : (dag.size d1 <= dag.size d2)%N)
  : gensym_ok G d1 -> gensym_ok G d2.
Proof using Type. cbv [gensym_ok]; intros; specialize_under_binders_by eassumption; lia. Qed.

Lemma gensym_ok_merge_node G d {descr:description} n
  : gensym_ok G d -> gensym_ok G (snd (dag.merge_node n d)).
Proof using Type. apply gensym_ok_size_Proper, dag.size_merge_node_le. Qed.

Lemma gensym_ok_sum_idx {descr : description} G :
  forall idxs s,
  forall d, gensym_ok G d ->
  gensym_ok G (snd (sum_idx d s idxs)).
Proof.
  intros. cbv [sum_idx]. destruct idxs as [| i [| i' idxs''] ].
  - apply gensym_ok_merge_node. apply H.
  - simpl. apply H.
  - apply gensym_ok_merge_node. apply H.
Qed.

Lemma empty_gensym_dag_ok : gensym_dag_ok (fun _ => None) dag.empty.
Proof using Type.
  cbv [gensym_dag_ok dag_ok gensym_ok].
  repeat match goal with |- _ /\ _ => split end; try exact _; intros *;
    rewrite ?dag.lookup_empty; try congruence.
Qed.

Lemma eval_merge_node {descr descr' descr'' descr'''} :
  forall G d, gensym_dag_ok G d ->
  forall op args n, let e := (op, args) in
  eval G d (ExprApp (op, List.map ExprRef args)) n ->
  eval G (snd (@merge_node descr e d)) (ExprRef (fst (@merge_node descr' e d))) n /\
  gensym_dag_ok G (snd (@merge_node descr'' e d)) /\
  forall i e', eval G d i e' -> eval G (snd (@merge_node descr''' e d)) i e'.
Proof using Type.
  intros.
  cbv beta delta [merge_node].
  inversion H0; subst.
  cbv [gensym_dag_ok dag_ok] in *; destruct_head'_and.
  repeat match goal with |- _ /\ _ => split end; try exact _.
  1: econstructor; try eassumption.
  all: eauto using Forall2_weaken, eval_weaken_merge_node.
  all: try now apply gensym_ok_merge_node.
  { now rewrite dag.lookup_merge_node' by assumption. }
  { apply @dag.merge_node_all_nodes_ok; try assumption.
    cbv [e node_ok]; intros; inversion_pair; subst; cbn [interp_op] in *.
    break_innermost_match_hyps; inversion_option; subst.
    cbv [gensym_ok] in *.
    specialize_under_binders_by eassumption; lia. }
  { intros *; rewrite dag.lookup_merge_node by assumption.
    break_innermost_match; inversion 1; subst; specialize_under_binders_by eassumption; destruct_head'_ex.
    all: eauto using eval_weaken_merge_node.
    reflect_hyps; destruct_head'_and; subst.
    lazymatch goal with
    | [ |- context[snd (@dag.merge_node ?descr ?e ?d)] ]
      => replace (dag.size d) with (fst (@dag.merge_node descr e d))
        by (rewrite dag.fst_merge_node; break_innermost_match; congruence)
    end.
    eexists; econstructor;
      [ rewrite dag.lookup_merge_node' by assumption; reflexivity
      | eauto using Forall2_weaken, eval_weaken_merge_node .. ]. }
Qed.

Lemma sth_about_snd : forall {X Y} (x : X) (y : Y) (z : X*Y), z = (x, y) -> y = snd z.
Proof.
  intros. assert (H': snd z = snd (x, y)).
  - f_equal. apply H.
  - simpl in H'. symmetry. apply H'.
Qed.

Lemma gensym_ok_split_carry_aux {descr : description} G :
  forall carry s,
  forall d, gensym_ok G d ->
  gensym_ok G (snd (split_carry_aux d s carry)).
Proof.
  intros carry. induction carry as [| i carry' IH].
  - intros. simpl. apply H.
  - intros. destruct carry' as [| i' carry''].
    + simpl. apply H.
    + remember (i' :: carry'') as carry'. simpl. destruct carry' as [| i'_ carry''_].
      -- simpl. apply H.
      -- remember (i'_ :: carry''_) as carry'.
      destruct (sum_idx d s i) as [adc_arg_1 d1] eqn:E1.
      destruct (sum_idx d1 s (fold_right (app (A:=idx)) [] carry')) as [adc_arg_2 d2] eqn:E2.
      destruct (merge_node (addcarry s, [adc_arg_1; adc_arg_2]) d2) as [i1 d3] eqn:E3.
      destruct (split_carry_aux d3 s carry') as [i2 d4] eqn:E4.
      simpl. rewrite (sth_about_snd _ _ _ E4). apply IH. clear i2 d4 E4.
      rewrite (sth_about_snd _ _ _ E3). apply gensym_ok_merge_node. clear i1 d3 E3.
      rewrite (sth_about_snd _ _ _ E2). apply gensym_ok_sum_idx. clear adc_arg_2 d2 E2.
      rewrite (sth_about_snd _ _ _ E1). apply gensym_ok_sum_idx. apply H.
Qed.

Lemma gensym_dag_ok_split_carry_aux {descr : description} G :
  forall carry s,
  forall d, gensym_dag_ok G d ->
  gensym_dag_ok G (snd (split_carry_aux d s carry)).
Proof.
  intros carry. induction carry as [| i carry' IH].
  - intros. simpl. apply H.
  - intros. remember (eval_merge_node _ _ H) as H'. clear HeqH'. destruct carry' as [| i' carry''].
    + simpl. apply H.
    + remember (i' :: carry'') as carry'. simpl. destruct carry' as [| i'_ carry''_].
      -- simpl. apply H.
      -- remember (i'_ :: carry''_) as carry'.
        destruct (sum_idx d s i) as [adc_arg_1 d1] eqn:E1.
        destruct (sum_idx d1 s (fold_right (app (A:=idx)) [] carry')) as [adc_arg_2 d2] eqn:E2.
        destruct (merge_node (addcarry s, [adc_arg_1; adc_arg_2]) d2) as [i1 d3] eqn:E3.
        destruct (split_carry_aux d3 s carry') as [i2 d4] eqn:E4.
        simpl. rewrite (sth_about_snd _ _ _ E4). apply IH. clear i2 d4 E4.
        cbv [gensym_dag_ok]. split.
        ++ rewrite (sth_about_snd _ _ _ E3). apply gensym_ok_merge_node. clear i1 d3 E3.
           rewrite (sth_about_snd _ _ _ E2). apply gensym_ok_sum_idx. clear adc_arg_2 d2 E2.
           rewrite (sth_about_snd _ _ _ E1). apply gensym_ok_sum_idx. apply H.
        ++ cbv [dag_ok]. Admitted.
(* Qed.
 *)
Lemma gensym_ok_split_carry {descr : description} G :
  forall carry s,
  forall d, gensym_ok G d ->
  gensym_ok G (snd (split_carry d s carry)).
Proof.
  intros. cbv [split_carry]. apply gensym_ok_split_carry_aux. apply H.
Qed.

Print split_carries.

Lemma gensym_ok_split_carries {descr : description} G :
  forall carries s,
  forall d, gensym_ok G d ->
  gensym_ok G (snd (split_carries d s carries)).
Proof.
  intros carries. induction carries as [| carry more_carries IH].
  - intros. simpl. apply H.
  - intros. simpl.
    destruct (split_carry d s carry) as [some_addends d'] eqn:E1.
    destruct (split_carries d' s more_carries) as [more_addends d''] eqn:E2.
    simpl. rewrite (sth_about_snd _ _ _ E2). apply IH.
    rewrite (sth_about_snd _ _ _ E1). apply gensym_ok_split_carry.
    apply H.
Qed.

Print eval.

Require Import coqutil.Tactics.autoforward coqutil.Decidable coqutil.Tactics.Tactics.
Global Set Default Goal Selector "1".

Print eval.
Print Forall2.
Print gensym_dag_ok.
Print gensym_ok.
Print dag_ok.
Print dag.ok.
Print dag.size_ok.
Print standardize_adc_sum.
Print symbol.
Print eval.

(* Lemma eval_standardize_adc_sum {descr : description}:
  forall G d s, gensym_dag_ok G d ->
  forall op args n, let e := (op, args) in
  eval G d (ExprApp (op, List.map ExprRef args)) n ->
  let result := standardize_adc_sum d args s in
  eval G (snd result) (ExprApp (op, List.map ExprRef (fst result))) n (*/\
  gensym_dag_ok G (snd result) /\
  forall i e', eval G d i e' -> eval G (snd result) i e'*).
Proof.
  intros.

(* 
forall idxs o s,
  forall d, gensym_dag_ok G d ->
  sum o = true ->
  
  gensym_dag_ok G (snd (standardize_adc_sum d idxs s)) /\ *)
  

Lemma eval_standardize_adc {descr : description} G :
  forall idxs o s,
  forall d, gensym_dag_ok G d ->
  eval G d e n ->
  eval G (snd (merge e d)) (ExprRef (fst (merge e d))) n /\
  gensym_dag_ok G (snd (merge e d)) /\
  forall i e', eval G d i e' -> eval G (snd (merge e d)) i e'.
Proof.
  intros idxs o s d. cbv [gensym_dag_ok standardize_adc_sum]. intros [H1 H2] H3. split.
  - destruct (withadc_without d s idxs) as [withadc without] eqn:E1.
    destruct (split_carries d s (merge_carries withadc)) as [standard_withadc d'] eqn:E2.
    simpl. rewrite (sth_about_snd _ _ _ E2). apply gensym_ok_split_carries. apply H1.
  -  *)

Lemma eval_merge {descr:description} G :
  forall e n,
  forall d, gensym_dag_ok G d ->
  eval G d e n ->
  eval G (snd (merge e d)) (ExprRef (fst (merge e d))) n /\
  gensym_dag_ok G (snd (merge e d)) /\
  forall i e', eval G d i e' -> eval G (snd (merge e d)) i e'.
Proof using Type. Admitted.
  (* induction e; intros; eauto; [].
  rename n0 into v.

  set (merge _ _) as m; cbv beta iota delta [merge] in m; fold @merge in m.
  destruct n as (op&args).
  repeat match goal with
    m := let x := ?A in @?B x |- _ =>
    let y := fresh x in
    set A as y;
    let m' := eval cbv beta in (B y) in
    change m' in (value of m)
  end.

  inversion H1; clear H1 ; subst.

  cbn [fst snd] in *.
  assert (gensym_dag_ok G (snd idxs_d) /\
    Forall2 (fun i v => eval G (snd idxs_d) (ExprRef i) v) (fst idxs_d) args' /\
    forall i e', eval G d i e' -> eval G (snd idxs_d) i e'
  ) as HH; [|destruct HH as(?&?&?)].
  { clear m idxs H6 v op; revert dependent d; revert dependent args'.
    induction H; cbn; intros; inversion H4; subst;
      split_and; pose proof @Forall2_weaken; typeclasses eauto 8 with core. }
  clearbody idxs_d.

  enough (eval G (snd idxs_d) (ExprApp (op, map ExprRef idxs)) v) by
    (unshelve (let lem := open_constr:(eval_merge_node _ _ ltac:(eassumption) op idxs v) in
               edestruct lem as (?&?&?)); eauto); clear m.

  pose proof length_Forall2 H4; pose proof length_Forall2 H2.

  cbn [fst snd] in *; destruct (commutative op) eqn:?; cycle 1; subst idxs.

  { econstructor; eauto.
    eapply ListUtil.Forall2_forall_iff; rewrite map_length; try congruence; [].
    intros i Hi.
    unshelve (epose proof (proj1 (ListUtil.Forall2_forall_iff _ _ _ _ _ _) H2 i _));
      shelve_unifiable; try congruence; [].
    rewrite ListUtil.map_nth_default_always. eapply H8. }

  pose proof N.Sort.Permuted_sort (fst idxs_d) as Hperm.
  eapply (Permutation.Permutation_Forall2 Hperm) in H2.
  case H2 as (argExprs&Hperm'&H2).
  eapply permute_commutative in H6; try eassumption; [].
  epose proof Permutation.Permutation_length Hperm.
  epose proof Permutation.Permutation_length Hperm'.

  { econstructor; eauto.
    eapply ListUtil.Forall2_forall_iff; rewrite map_length; try congruence; [|].
    { setoid_rewrite <-H8. setoid_rewrite <-H9. eassumption. }
    intros i Hi.
    unshelve (epose proof (proj1 (ListUtil.Forall2_forall_iff _ _ _ _ _ _) H2 i _));
      shelve_unifiable; try trivial; [|].
    { setoid_rewrite <-H8. setoid_rewrite <-H9. eassumption. }
    rewrite ListUtil.map_nth_default_always. eapply H10. }
  Unshelve. all : constructor.
Qed. *)

Definition zconst s (z:Z) := const (Z.land z (Z.ones (Z.of_N s)))%Z.

Section WithContext.
  Context (ctx : symbol -> option Z).
  Fixpoint interp_expr (e : expr) : option Z :=
    match e with
    | ExprApp (o, arges) =>
        args <- Option.List.lift (List.map interp_expr arges);
        interp_op ctx o args
    | _ => None
    end%option.
End WithContext.
Definition interp0_expr := interp_expr (fun _ => None).

Lemma eval_interp_expr G e : forall d v, interp_expr G e = Some v -> eval G d e v.
Proof using Type.
  induction e; cbn; try discriminate; intros.
  case n in *; cbn [fst snd] in *.
  destruct (Option.List.lift _) eqn:? in *; try discriminate.
  econstructor; try eassumption; [].
  clear dependent v.
  revert dependent l0.
  induction H; cbn in *.
  { inversion 1; subst; eauto. }
  destruct (interp_expr _) eqn:? in *; cbn in *; try discriminate; [].
  destruct (fold_right _ _ _) eqn:? in *; cbn in *; try discriminate; [].
  specialize (fun d => H d _ eq_refl).
  inversion 1; subst.
  econstructor; trivial; [].
  eapply IHForall; eassumption.
Qed.

Lemma eval_interp0_expr e v (H : interp0_expr e = Some v) : forall G d, eval G d e v.
Proof using Type.
  cbv [interp0_expr]; intros.
  eapply eval_interp_expr, eval_weaken_symbols in H; [eassumption|congruence].
Qed.

Local Open Scope Z_scope.

Import coqutil.Tactics.Tactics.
Ltac t:= match goal with
  | _ => progress intros
  | H : eval _ _ (ExprApp _) _ |- _ => inversion H; clear H; subst
  | H : Forall _ (cons _ _) |- _ => inversion H; clear H; subst
  | H : Forall _ nil |- _ => inversion H; clear H; subst
  | H : Forall2 _ (cons _ _) _ |- _ => inversion H; clear H; subst
  | H : Forall2 _ nil _ |- _ => inversion H; clear H; subst
  | H : Forall2 _ _ (cons _ _) |- _ => inversion H; clear H; subst
  | H : Forall2 _ _ nil |- _ => inversion H; clear H; subst
  | H : _ = true |- _ => autoforward with typeclass_instances in H
  | H : forall b, _ |- _ => pose proof (H _ ltac:(eassumption) _ _ ltac:(eassumption)); clear H
  | H : eval _ ?d ?e ?v1, G: eval _ ?d ?e ?v2 |- _ =>
      assert_fails (constr_eq v1 v2);
      eapply (eval_eval _ d e v1 H v2) in G
  | _ => progress cbv [interp_op] in *
  | _ => progress cbn [fst snd] in *
  | _ => progress destruct_one_match
  | _ => progress Option.inversion_option
  | _ => progress subst
  end.

Lemma bound_sum' G d
  es (He : Forall (fun e => forall b, bound_expr e = Some b ->
       forall (d : dag) (v : Z), eval G d e v -> (0 <= v <= b)%Z) es)
  : forall
  bs (Hb : Option.List.lift (map bound_expr es) = Some bs)
  vs (Hv : Forall2 (eval G d) es vs)
  , (0 <= fold_right Z.add 0 vs <= fold_right Z.add 0 bs)%Z.
Proof using Type.
  induction He; cbn in *; repeat t.
  { cbv [fold_right]; Lia.lia. }
  destruct (bound_expr _) eqn:? in *; cbn in *; repeat t.
  destruct (fold_right (B:=option _) _) eqn:? in *; cbn in *; repeat t.
  specialize (IHHe _ ltac:(eassumption) _ ltac:(eassumption)); cbn.
  specialize (H _ ltac:(exact eq_refl) _ _ ltac:(eassumption)).
  Lia.lia.
Qed.

Require Import Util.ZRange.LandLorBounds.
Lemma eval_bound_expr G e b : bound_expr e = Some b ->
  forall d v, eval G d e v -> (0 <= v <= b)%Z.
Proof using Type.
  revert b; induction e; simpl bound_expr; BreakMatch.break_match;
    inversion 2; intros; inversion_option; subst;
    try match goal with H : context [set_slice] |- _ => shelve end;
    cbv [interp_op] in *;
    BreakMatch.break_match_hyps; inversion_option; subst;
    rewrite ?Z.ldiff_ones_r, ?Z.land_ones, ?Z.ones_equiv;
    cbv [Z.b2z];
    try match goal with |- context [(?a mod ?b)%Z] => unshelve epose proof Z.mod_pos_bound a b ltac:(eapply Z.pow_pos_nonneg; Lia.lia) end;
    repeat t;
    try (Z.div_mod_to_equations; Lia.lia).
  { clear dependent args'0.
    epose proof bound_sum' _ ltac:(eassumption) _ ltac:(eassumption) _ ltac:(eassumption) _ ltac:(eassumption).
    split; try Lia.lia.
    eapply Z.min_glb_iff; split; try Lia.lia.
    etransitivity. eapply Zmod_le.
    all : try Lia.lia. }
  Unshelve. {
    repeat t.
    pose proof Z.log2_nonneg z; pose proof Z.log2_nonneg z0.
    rewrite !Z.shiftl_0_r.
    split.
    { eapply Z.lor_nonneg; split; try eapply Z.land_nonneg; try eapply Z.ldiff_nonneg; Lia.lia. }
    eapply Z.le_bitwise.
    { eapply Z.lor_nonneg; split; try eapply Z.land_nonneg; try eapply Z.ldiff_nonneg; Lia.lia. }
    { eapply Z.lor_nonneg; split; try eapply Z.land_nonneg; try eapply Z.ldiff_nonneg;
        left; try eapply Z.ones_nonneg; Lia.lia. }
    { intros i Hi.
      Z.rewrite_bitwise.
      destr (i <? Z.of_N sz);
        rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_l, ?Bool.orb_false_r.
      { clear -H Hi.
        destr (i <? Z.succ (Z.log2 z0)).
        { eapply Bool.le_implb, Bool.implb_true_r. }
        rewrite Z.bits_above_log2; cbn; trivial; try Lia.lia.
        destruct H as [H' H]; eapply Z.log2_le_mono in H. Lia.lia. }
      { clear -H0 Hi.
        destr (i <? Z.succ (Z.log2 z)).
        { eapply Bool.le_implb, Bool.implb_true_r. }
        rewrite Z.bits_above_log2; cbn; trivial; try Lia.lia.
        destruct H0 as [? H0]; eapply Z.log2_le_mono in H0. Lia.lia. } } }
Qed.

Lemma bound_sum G d es
  bs (Hb : Option.List.lift (map bound_expr es) = Some bs)
  vs (Hv : Forall2 (eval G d) es vs)
  : (0 <= fold_right Z.add 0 vs <= fold_right Z.add 0 bs)%Z.
Proof using Type.
  eapply bound_sum' in Hb; eauto.
  eapply Forall_forall; intros.
  eapply eval_bound_expr; eauto.
Qed.


Definition isCst (e : expr) :=
  match e with ExprApp ((const _), []) => true | _ => false end.

Module Rewrite.
Class Ok r := rwok : forall G d e v, eval G d e v -> eval G d (r e) v.

Ltac resolve_match_using_hyp :=
  match goal with |- context[match ?x with _ => _ end] =>
  match goal with H : x = ?v |- _ =>
      let h := Head.head v in
      is_constructor h;
      rewrite H
  end end.

Ltac step := match goal with
  | |- Ok ?r => cbv [Ok r]; intros
  | _ => solve [trivial | contradiction]
  |  _ => resolve_match_using_hyp
  | _ => inversion_option_step

  | H : _ = ?v |- _ => is_var v; progress subst v
  | H : ?v = _ |- _ => is_var v; progress subst v

  | H : eval _ ?d ?e ?v1, G: eval _ ?d ?e ?v2 |- _ =>
      assert_fails (constr_eq v1 v2);
      eapply (eval_eval _ d e v1 H v2) in G
  | |- eval _ ?d ?e ?v =>
      match goal with
        H : eval _ d e ?v' |- _ =>
            let Heq := fresh in
            enough (Heq : v = v') by (rewrite Heq; exact H);
            try (clear H; clear e)
      end

  | H: interp_op _ (const _) nil = Some _ |- _ => inversion H; clear H; subst
  | H: interp0_op _ _ = Some _ |- _ => eapply interp_op_interp0_op in H
  | H: interp0_expr _ = Some _ |- _ => eapply eval_interp0_expr in H
  | H: bound_expr _ = Some _ |- _ => eapply eval_bound_expr in H; eauto; [ ]

  | H : (?x <=? ?y)%N = ?b |- _ => is_constructor b; destruct (N.leb_spec x y); (inversion H || clear H)
  | H : andb _ _ = true |- _ => eapply Bool.andb_prop in H; case H as (?&?)
  | H : N.eqb ?n _ = true |- _ => eapply N.eqb_eq in H; try subst n
  | H : Z.eqb ?n _ = true |- _ => eapply Z.eqb_eq in H; try subst n
  | H : expr_beq ?a ?b = true |- _ => replace a with b in * by (symmetry;exact (expr_beq_true a b H)); clear H
  | _ => progress destruct_one_match_hyp
  | _ => progress destruct_one_match

  | H : eval _ _ ?e _ |- _ => assert_fails (is_var e); inversion H; clear H; subst
  | H : Forall2 (eval _ _) (cons _ _) _ |- _ => inversion H; clear H; subst
  | H : Forall2 (eval _ _) _ (cons _ _) |- _ => inversion H; clear H; subst
  | H : Forall2 _ _ nil |- _ => inversion H; clear H; subst
  | H : Forall2 _ nil _ |- _ => inversion H; clear H; subst

  | _ => progress cbn [fst snd map option_map] in *
  end.

Ltac Econstructor :=
  match goal with
  | |- Forall2 (eval _ _) _ _ =>  econstructor
  | |- eval _ _ ?e _ => econstructor
  end.

Ltac t := repeat (step || Econstructor || eauto || (progress cbn [interp0_op interp_op] in * ) ).

Definition slice0 :=
  fun e => match e with
    ExprApp (slice 0 s, [(ExprApp ((addZ|mulZ|negZ|shlZ|shrZ|andZ|orZ|xorZ) as o, args))]) =>
        ExprApp ((match o with addZ=>add s|mulZ=>mul s|negZ=>neg s|shlZ=>shl s|shrZ => shr s|andZ => and s| orZ => or s|xorZ => xor s |_=>old 0%N 999999%N end), args)
      | _ => e end.
Global Instance slice0_ok : Ok slice0. Proof using Type. t. Qed.

Definition slice01_addcarryZ :=
  fun e => match e with
    ExprApp (slice 0 1, [(ExprApp (addcarryZ s, args))]) =>
        ExprApp (addcarry s, args)
      | _ => e end.
Global Instance slice01_addcarryZ_ok : Ok slice01_addcarryZ.
Proof using Type. t; rewrite ?Z.shiftr_0_r, ?Z.land_ones, ?Z.shiftr_div_pow2; trivial; Lia.lia. Qed.

Definition slice01_subborrowZ :=
  fun e => match e with
    ExprApp (slice 0 1, [(ExprApp (subborrowZ s, args))]) =>
        ExprApp (subborrow s, args)
      | _ => e end.
Global Instance slice01_subborrowZ_ok : Ok slice01_subborrowZ.
Proof using Type. t; rewrite ?Z.shiftr_0_r, ?Z.land_ones, ?Z.shiftr_div_pow2; trivial; Lia.lia. Qed.

Definition slice_set_slice :=
  fun e => match e with
    ExprApp (slice 0 s1, [ExprApp (set_slice 0 s2, [_; e'])]) =>
      if N.leb s1 s2 then ExprApp (slice 0 s1, [e']) else e | _ => e end.
Global Instance slice_set_slice_ok : Ok slice_set_slice.
Proof using Type. t. f_equal. Z.bitblast. Qed.

Definition set_slice_set_slice :=
  fun e => match e with
    ExprApp (set_slice lo1 s1, [ExprApp (set_slice lo2 s2, [x; e']); y]) =>
      if andb (N.eqb lo1 lo2) (N.leb s2 s1) then ExprApp (set_slice lo1 s1, [x; y]) else e | _ => e end.
Global Instance set_slice_set_slice_ok : Ok set_slice_set_slice.
Proof using Type. t. f_equal. Z.bitblast. Qed.

Definition set_slice0_small :=
  fun e => match e with
    ExprApp (set_slice 0 s, [x; y]) =>
      match bound_expr x, bound_expr y with Some a, Some b =>
      if Z.leb a (Z.ones (Z.of_N s)) && Z.leb b (Z.ones (Z.of_N s)) then y
      else e | _, _ => e end | _ => e end%bool.
Global Instance set_slice0_small_ok : Ok set_slice0_small.
Proof using Type.
  t.
  eapply Zle_bool_imp_le in H0; rewrite Z.ones_equiv in H0; eapply Z.lt_le_pred in H0.
  eapply Zle_bool_imp_le in H1; rewrite Z.ones_equiv in H1; eapply Z.lt_le_pred in H1.
  assert ((0 <= y < 2^Z.of_N sz)%Z) by Lia.lia; clear dependent z.
  assert ((0 <= y0 < 2^Z.of_N sz)%Z) by Lia.lia; clear dependent z0.
  rewrite ?Z.shiftl_0_r, Z.land_ones, Z.mod_small by Lia.lia.
  destruct (Z.eq_dec y 0); subst.
  { rewrite Z.ldiff_0_l, Z.lor_0_r; trivial. }
  rewrite Z.ldiff_ones_r_low, Z.lor_0_r; try Lia.lia.
  eapply Z.log2_lt_pow2; Lia.lia.
Qed.

Definition truncate_small :=
  fun e => match e with
    ExprApp (slice 0%N s, [e']) =>
      match bound_expr e' with Some b =>
      if Z.leb b (Z.ones (Z.of_N s))
      then e'
      else e | _ => e end | _ => e end.
Global Instance truncate_small_ok : Ok truncate_small. Proof using Type. t; []. cbn in *; eapply Z.land_ones_low_alt_ones; eauto. firstorder. Lia.lia. Qed.

Definition addcarry_bit :=
  fun e => match e with
    ExprApp (addcarry s, ([ExprApp (const a, nil);b])) =>
      if option_beq Z.eqb (bound_expr b) (Some 1) then
      match interp0_op (addcarry s) [a; 0], interp0_op (addcarry s) [a; 1] with
      | Some 0, Some 1 => b
      | Some 0, Some 0 => ExprApp (const 0, nil)
      | _, _ => e
      end else e | _ => e end%Z%bool.
Global Instance addcarry_bit_ok : Ok addcarry_bit.
Proof using Type.
  repeat step;
    [instantiate (1:=G) in E0; instantiate (1:=G) in E1|];
    destruct (Reflect.reflect_eq_option (eqA:=Z.eqb) (bound_expr e) (Some 1%Z)) in E;
      try discriminate; repeat step;
    assert (y0 = 0 \/ y0 = 1)%Z as HH by Lia.lia; case HH as [|];
      subst; repeat step; repeat Econstructor; cbn; congruence.
Qed.

Definition addoverflow_bit :=
  fun e => match e with
    ExprApp (addoverflow s, ([ExprApp (const a, nil);b])) =>
      if option_beq Z.eqb (bound_expr b) (Some 1%Z) then
      match interp0_op (addoverflow s) [a; 0] , interp0_op (addoverflow s) [a; 1] with
      | Some 0, Some 1 => b
      | Some 0, Some 0 => ExprApp (const 0, nil)
      | _, _ => e
      end else e | _ => e end%Z%bool.
Global Instance addoverflow_bit_ok : Ok addoverflow_bit.
Proof using Type.
  repeat step;
    [instantiate (1:=G) in E0; instantiate (1:=G) in E1|];
    destruct (Reflect.reflect_eq_option (eqA:=Z.eqb) (bound_expr e) (Some 1)%Z) in E;
      try discriminate; repeat step;
    assert (y0 = 0 \/ y0 = 1)%Z as HH by Lia.lia; case HH as [|];
      subst; repeat step; repeat Econstructor; cbn; congruence.
Qed.

Definition addbyte_small :=
  fun e => match e with
    ExprApp (add (8%N as s), args) =>
      match Option.List.lift (List.map bound_expr args) with
      | Some bounds =>
          if Z.leb (List.fold_right Z.add 0%Z bounds) (Z.ones (Z.of_N s))
          then ExprApp (add 64%N, args)
          else e | _ => e end | _ =>  e end.
Global Instance addbyte_small_ok : Ok addbyte_small.
Proof using Type.
  t; f_equal.
  eapply bound_sum in H2; eauto.
  rewrite Z.ones_equiv in E0; rewrite !Z.land_ones, !Z.mod_small; try Lia.lia;
    replace (Z.of_N 8) with 8 in * by (vm_compute; reflexivity);
    replace (Z.of_N 64) with 64 in * by (vm_compute; reflexivity); Lia.lia.
Qed.

Definition addcarry_small :=
  fun e => match e with
    ExprApp (addcarry s, args) =>
      match Option.List.lift (List.map bound_expr args) with
      | Some bounds =>
          if Z.leb (List.fold_right Z.add 0%Z bounds) (Z.ones (Z.of_N s))
          then (ExprApp (const 0, nil))
          else e | _ => e end | _ =>  e end.
Global Instance addcarry_small_ok : Ok addcarry_small.
Proof using Type.
  t; f_equal.
  eapply bound_sum in H2; eauto.
  rewrite Z.ones_equiv in E0; rewrite Z.shiftr_div_pow2, Z.div_small; cbn; Lia.lia.
Qed.

Lemma signed_small s v (Hv : (0 <= v <= Z.ones (Z.of_N s-1))%Z) : signed s v = v.
Proof using Type.
  destruct (N.eq_dec s 0); subst; cbv [signed].
  { rewrite Z.land_0_r. cbn in *; Lia.lia. }
  rewrite !Z.land_ones, !Z.shiftl_mul_pow2, ?Z.add_0_r, ?Z.mul_1_l by Lia.lia.
  rewrite Z.ones_equiv in Hv.
  rewrite Z.mod_small; try ring.
  enough (2 ^ Z.of_N s = 2 ^ (Z.of_N s - 1) + 2 ^ (Z.of_N s - 1))%Z; try Lia.lia.
  replace (Z.of_N s) with (1+(Z.of_N s-1))%Z at 1 by Lia.lia.
  rewrite Z.pow_add_r; try Lia.lia.
Qed.

Definition addoverflow_small :=
  fun e => match e with
    ExprApp (addoverflow s, ([_]|[_;_]|[_;_;_]) as args) =>
      match Option.List.lift (List.map bound_expr args) with
      | Some bounds =>
          if Z.leb (List.fold_right Z.add 0%Z bounds) (Z.ones (Z.of_N s-1))
          then (ExprApp (const 0, nil))
          else e | _ => e end | _ =>  e end.
Global Instance addoverflow_small_ok : Ok addoverflow_small.
Proof using Type.
  t; cbv [Option.List.lift Option.bind fold_right] in *;
  BreakMatch.break_match_hyps; Option.inversion_option; t;
  epose proof Z.ones_equiv (Z.of_N s -1).
  all : rewrite Z.land_ones, !Z.mod_small, !signed_small, !Z.eqb_refl; trivial.
  all : try split; try Lia.lia.
  all : replace (Z.of_N s) with (1+(Z.of_N s-1))%Z at 1 by Lia.lia;
  rewrite Z.pow_add_r; try Lia.lia.
  all : destruct s; cbn in E0; Lia.lia.
Qed.

Definition constprop :=
  fun e => match interp0_expr e with
           | Some v => ExprApp (const v, nil)
           | _ => e end.
Global Instance constprop_ok : Ok constprop.
Proof using Type. t. f_equal; eauto using eval_eval. Qed.

(* convert unary operations to slice *)
Definition unary_truncate :=
  fun e => match e with
    ExprApp (o, [x]) =>
    match unary_truncate_size o with
    | Some (-1)%Z => x
    | Some 0%Z => ExprApp (const 0, nil)
    | Some (Zpos p)
      => ExprApp (slice 0%N (Npos p), [x])
    | _ => e end | _ => e end.

Global Instance unary_truncate_ok : Ok unary_truncate.
Proof using Type.
  t.
  all: repeat first [ progress cbv [unary_truncate_size] in *
                    | progress cbn [fold_right Z.of_N] in *
                    | progress change (Z.of_N 0) with 0 in *
                    | progress change (Z.ones 0) with 0 in *
                    | apply (f_equal (@Some _))
                    | lia
                    | progress autorewrite with zsimplify_const
                    | progress break_innermost_match_hyps
                    | match goal with
                      | [ H : Z.of_N ?s = 0 |- _ ] => is_var s; destruct s; try lia
                      | [ H : Z.of_N ?s = Z.pos _ |- _ ] => is_var s; destruct s; try lia
                      | [ H : Z.pos _ = Z.pos _ |- _ ] => inversion H; clear H
                      end
                    | progress t ].
Qed.

Lemma fold_right_filter_identity_gen A B C f init F G xs
      (Hid : forall x y, F x = false -> G (f x y) = G y)
      (HProper : forall x y y', G y = G y' -> G (f x y) = G (f x y'))
  : G (@fold_right A B f init (filter F xs)) = G (@fold_right A B f init xs) :> C.
Proof.
  induction xs as [|x xs IH]; [ | specialize (Hid x) ]; cbn; break_innermost_match; cbn; rewrite ?Hid by auto; auto; congruence.
Qed.

Lemma fold_right_filter_identity A B f init F xs
      (Hid : forall x y, F x = false -> f x y = y)
  : @fold_right A B f init (filter F xs) = @fold_right A B f init xs.
Proof.
  apply fold_right_filter_identity_gen with (G:=id); cbv [id]; intuition (subst; eauto).
Qed.

Lemma signed_0 s : signed s 0 = 0%Z.
Proof using Type.
  destruct (N.eq_dec s 0); subst; trivial.
  cbv [signed].
  rewrite !Z.land_ones, !Z.shiftl_mul_pow2, ?Z.add_0_r, ?Z.mul_1_l by Lia.lia.
  rewrite Z.mod_small; try ring.
  split; try (eapply Z.pow_lt_mono_r; Lia.lia).
  eapply Z.pow_nonneg; Lia.lia.
Qed.
Hint Rewrite signed_0 : zsimplify_const zsimplify zsimplify_fast.
Global Hint Resolve signed_0 : zarith.

Lemma interp_op_drop_identity o id : identity o = Some id ->
  forall G xs, interp_op G o xs = interp_op G o (List.filter (fun v => negb (Z.eqb v id)) xs).
Proof using Type.
  destruct o; cbn [identity]; intro; inversion_option; subst; intros G xs; cbn [interp_op]; f_equal.
  all: break_innermost_match_hyps; inversion_option; subst.
  all: rewrite ?fold_right_map.
  all: rewrite ?fold_right_filter_identity by now intros; reflect_hyps; subst; auto with zarith; autorewrite with zsimplify_const; lia.
  all: repeat first [ reflexivity
                    | progress autorewrite with zsimplify_const ].
  { (idtac + symmetry); apply fold_right_filter_identity_gen with (G:=fun x => Z.land x _).
    all: intros; reflect_hyps; subst.
    all: rewrite <- ?Z.land_assoc, ?(Z.land_comm (Z.ones _)), ?Z.land_ones in * by lia.
    all: push_Zmod; pull_Zmod.
    all: congruence. }
Qed.

Lemma interp_op_drop_identity_after_0 o id : identity_after_0 o = Some id ->
  forall G x xs, interp_op G o (x :: xs) = interp_op G o (x :: List.filter (fun v => negb (Z.eqb v id)) xs).
Proof using Type.
  destruct o; cbn [identity_after_0]; intro; inversion_option; subst; intros G x xs; cbn [interp_op]; f_equal.
  all: rewrite ?fold_right_map.
  all: rewrite ?fold_right_filter_identity by now intros; reflect_hyps; subst; auto with zarith; autorewrite with zsimplify_const; lia.
  all: repeat first [ reflexivity
                    | progress autorewrite with zsimplify_const ].
Qed.

Lemma interp_op_nil_is_identity o i (Hi : identity o = Some i)
  G : interp_op G o [] = Some i.
Proof using Type.
  destruct o; cbn [identity] in *; break_innermost_match_hyps; inversion_option; subst; cbn [interp_op fold_right]; f_equal.
  all: cbn [interp_op fold_right]; autorewrite with zsimplify_const; try reflexivity.
  { cbn [identity]; break_innermost_match; try reflexivity.
    rewrite Z.land_ones by lia; Z.rewrite_mod_small; try reflexivity;
      (* compat with older versions of Coq (needed for 8.11, not for 8.13) *)
      rewrite Z.mod_small; rewrite ?Z.log2_lt_pow2; cbn [Z.log2]; try lia. }
Qed.

Lemma interp_op_always_interps G o args
  : op_always_interps o = true -> interp_op G o args <> None.
Proof. destruct o; cbn; congruence. Qed.

Lemma interp0_op_always_interps o args
  : op_always_interps o = true -> interp0_op o args <> None.
Proof. apply interp_op_always_interps. Qed.

(* completeness check, just update the definition if this doesn't go through *)
Lemma interp_op_always_interps_complete o
  : op_always_interps o = false -> exists G args, interp_op G o args = None.
Proof.
  destruct o; cbn; try solve [ inversion 1 ]; intros _; do 2 try eapply ex_intro.
  all: repeat match goal with
              | [ |- match ?ev with [] => None | _ => _ end = None ] => let __ := open_constr:(eq_refl : ev = []) in cbv beta iota
              | [ |- match ?ev with _ :: _ => None | _ => _ end = None ] => let __ := open_constr:(eq_refl : ev = _ :: _) in cbv beta iota
              | [ |- None = None ] => reflexivity
              end.
  Unshelve. all: shelve_unifiable.
  all: lazymatch goal with
       | [ |- Z ] => exact 0%Z
       | [ |- _ -> option _ ] => intro; exact None
       | [ |- list _ ] => exact nil
       | _ => idtac
       end.
  all: fail_if_goals_remain ().
Qed.

Lemma invert_interp_op_associative o : associative o = true ->
  forall G x xs v, interp_op G o (x :: xs) = Some v ->
  exists v', interp_op G o xs = Some v' /\
  interp_op G o [x; v'] = Some v.
Proof using Type.
  destruct o; inversion 1; intros * HH; inversion HH; clear HH; subst; cbn;
    eexists; split; eauto; f_equal; try ring; try solve [Z.bitblast].
  { rewrite !Z.add_0_r, ?Z.land_ones; push_Zmod; pull_Zmod; Lia.lia. }
  { rewrite !Z.mul_1_r, ?Z.land_ones; push_Zmod; pull_Zmod; Lia.lia. }
Qed.

(** TODO: plausibly we want to define all associative operations in terms of some [make_associative_op] definition, so that we can separate out the binary operation reasoning from the fold and option reasoning *)
(* is it okay for associative to imply identity? *)
Lemma interp_op_associative_spec_fold o : associative o = true ->
  forall G xs, interp_op G o xs = fold_right (fun v acc => acc <- acc; interp_op G o [v; acc])%option (interp_op G o []) xs.
Proof using Type.
  intros H G; induction xs as [|x xs IHxs]; cbn [fold_right]; [ reflexivity | ].
  rewrite <- IHxs; clear IHxs.
  destruct o; inversion H; cbn [interp_op Option.bind fold_right]; f_equal.
  all: autorewrite with zsimplify_const.
  all: try solve [ Z.bitblast ].
  all: try solve [ rewrite ?Z.land_ones in *; push_Zmod; pull_Zmod; Lia.lia ].
Qed.

Lemma interp_op_associative_spec_id o : associative o = true ->
  forall G, interp_op G o [] = identity o.
Proof using Type.
  intros H G.
  pose proof (fun id H => interp_op_nil_is_identity o id H G) as H1.
  destruct o; inversion H; cbn [identity] in *; break_innermost_match_hyps; erewrite H1; try reflexivity.
Qed.

Lemma interp_op_associative_identity_Some o : associative o = true ->
  forall G xs vxs, interp_op G o xs = Some vxs -> Option.is_Some (identity o) = true.
Proof using Type.
  intros H G xs vxs H1; rewrite <- interp_op_associative_spec_id with (G:=G) by assumption.
  rewrite interp_op_associative_spec_fold in H1 by assumption.
  cbv [is_Some]; break_innermost_match; try reflexivity.
  exfalso.
  clear -H1.
  revert dependent vxs; induction xs as [|?? IH]; cbn in *; intros; inversion_option.
  unfold Option.bind at 1 in H1; break_innermost_match_hyps; eauto.
Qed.

Lemma interp_op_associative_spec_assoc o : associative o = true ->
  forall G ys vys, interp_op G o ys = Some vys ->
  forall   zs vzs, interp_op G o zs = Some vzs ->
  forall x, ((xy <- interp_op G o [x; vys]; interp_op G o [xy; vzs]) = (yz <- interp_op G o [vys; vzs]; interp_op G o [x; yz]))%option.
Proof.
  destruct o; inversion 1; intros * H1 * H2; cbn [interp_op fold_right Option.bind] in *.
  all: intros; autorewrite with zsimplify_const; f_equal; inversion_option.
  all: rewrite ?Z.land_ones by lia; push_Zmod; pull_Zmod; rewrite <- ?Z.land_ones by lia.
  all: try solve [ f_equal; lia ].
  all: try reflexivity.
  all: try solve [ Z.bitblast ].
  all: try lia.
Qed.

Lemma interp_op_associative_spec_concat o : associative o = true ->
  forall G xs, interp_op G o (List.concat xs) = (vxs <-- List.map (interp_op G o) xs; interp_op G o vxs)%option.
Proof using Type.
  intros H G; induction xs as [|x xs IHxs]; cbn [fold_right]; [ reflexivity | ].
  cbn [List.concat List.map Option.List.bind_list].
  rewrite interp_op_associative_spec_fold, fold_right_app, <- interp_op_associative_spec_fold by assumption.
  rewrite IHxs; clear IHxs.
  setoid_rewrite Option.List.bind_list_cps_id; rewrite <- Option.List.eq_bind_list_lift.
  destruct (Option.List.lift (map (interp_op G o) xs)) as [vxs|]; cbn [Option.bind].
  { revert vxs; clear xs.
    induction x as [|x xs IHxs]; intro vxs.
    { cbn [fold_right].
      destruct (interp_op G o []) as [id|] eqn:H'; cbn [Option.bind].
      { etransitivity; erewrite interp_op_drop_identity by (erewrite <- interp_op_associative_spec_id; eassumption); [ | reflexivity ].
        cbn [List.filter]; unfold negb at 2; break_innermost_match_step; reflect_hyps; try congruence. }
      { pose proof (interp_op_associative_identity_Some o H G vxs) as H1.
        rewrite interp_op_associative_spec_id in * by assumption.
        rewrite H' in *.
        cbn [is_Some] in *.
        destruct interp_op; try reflexivity; specialize (H1 _ eq_refl); congruence. } }
    { cbn [fold_right].
      rewrite IHxs; clear IHxs.
      symmetry; rewrite interp_op_associative_spec_fold by assumption; cbn [fold_right]; rewrite <- interp_op_associative_spec_fold by assumption.
      unfold Option.bind at 2; break_innermost_match_step; cbn [Option.bind]; [ | reflexivity ].
      symmetry; rewrite interp_op_associative_spec_fold by assumption; cbn [fold_right]; rewrite <- interp_op_associative_spec_fold by assumption.
      symmetry.
      setoid_rewrite interp_op_associative_spec_fold at 2; [ | assumption ].
      cbn [fold_right].
      setoid_rewrite <- interp_op_associative_spec_fold; [ | assumption ].
      destruct (interp_op G o vxs) eqn:?; cbn [Option.bind]; [ | cbv [Option.bind]; break_match; reflexivity ].
      eapply interp_op_associative_spec_assoc; eassumption. } }
  { etransitivity; [ | cbv [Option.bind]; break_innermost_match; reflexivity ].
    induction x as [|? ? IHx]; cbn; rewrite ?IHx; reflexivity. }
Qed.

Lemma interp_op_associative_app_bind G o : associative o = true ->
  forall xs ys,
  interp_op G o (xs ++ ys) = (vxs <- interp_op G o xs; vys <- interp_op G o ys; interp_op G o [vxs; vys])%option.
Proof using Type.
  intros.
  etransitivity; [ etransitivity; [ | refine (interp_op_associative_spec_concat o H G [xs; ys]) ] | ].
  { cbn [concat]; rewrite List.app_nil_r; reflexivity. }
  { cbn [map Option.List.bind_list].
    cbv [Option.bind]; break_innermost_match; reflexivity. }
Qed.

Lemma interp_op_associative_app G o : associative o = true ->
  forall xs vxs, interp_op G o xs = Some vxs ->
  forall ys vys, interp_op G o ys = Some vys ->
  interp_op G o (xs ++ ys) = interp_op G o [vxs; vys].
Proof using Type.
  intros H * H1 * H2.
  rewrite interp_op_associative_app_bind, H1, H2 by assumption.
  reflexivity.
Qed.

Lemma interp_op_associative_idempotent G o : associative o = true ->
  forall xs vxs, interp_op G o xs = Some vxs ->
  interp_op G o [vxs] = Some vxs.
Proof using Type.
  intros H xs vxs H1.
  pose proof (interp_op_associative_spec_concat o H G [ xs ]) as H2.
  cbn in H2.
  rewrite List.app_nil_r, H1 in H2; cbn [Option.bind] in *; congruence.
Qed.

Lemma interp_op_associative_cons o : associative o = true ->
  forall G x xs ys v,
  interp_op G o xs = Some v -> interp_op G o ys = Some v ->
  interp_op G o (x :: xs) = interp_op G o (x :: ys).
Proof using Type.
  intros H * H1 H2.
  etransitivity; [ etransitivity | ]; [ | refine (interp_op_associative_spec_concat o H _ [ [x]; xs]) | ].
  all: cbn [concat List.app map Option.List.bind_list]; rewrite ?List.app_nil_r.
  1: reflexivity.
  symmetry; etransitivity; [ etransitivity | ]; [ | refine (interp_op_associative_spec_concat o H _ [ [x]; ys]) | ].
  all: cbn [concat List.app map Option.List.bind_list]; rewrite ?List.app_nil_r.
  1: reflexivity.
  rewrite !H1, H2; cbn [Option.bind].
  reflexivity.
Qed.

Definition flatten_associative :=
  fun e => match e with
    ExprApp (o, args) =>
    if associative o then
      ExprApp (o, List.flat_map (fun e' =>
        match e' with
        | ExprApp (o', args') => if op_beq o o' then args' else [e']
        | _ => [e'] end) args)
    else e | _ => e end.
Global Instance flatten_associative_ok : Ok flatten_associative.
Proof using Type.
  repeat step.
  revert dependent v; induction H2; cbn.
  { econstructor; eauto. }
  intros ? H4.
  pose proof H4.
  eapply invert_interp_op_associative in H4; eauto. destruct H4 as (?&?&?).
  specialize (IHForall2 _ ltac:(eassumption)).
  inversion IHForall2; subst.
  destruct x as [i|[o' args''] ].
  { econstructor. { econstructor. eauto. eauto. }
    erewrite interp_op_associative_cons; eauto. }
  { destruct (op_beq_spec o o'); subst; cycle 1.
    { econstructor. { econstructor. eauto. eauto. }
      erewrite interp_op_associative_cons; eauto. }
    inversion H; clear H; subst.
    econstructor; eauto using Forall2_app.
    erewrite interp_op_associative_app; eauto. }
Qed.

Definition consts_commutative :=
  fun e => match e with
    ExprApp (o, args) =>
    if commutative o then
    let csts_exprs := List.partition isCst args in
    if associative o
    then match interp0_expr (ExprApp (o, fst csts_exprs)) with
         | Some v => ExprApp (o, ExprApp (const v, nil):: snd csts_exprs)
         | _ => ExprApp (o, fst csts_exprs ++ snd csts_exprs)
         end
    else ExprApp (o, fst csts_exprs ++ snd csts_exprs)
    else e | _ => e end.

Global Instance consts_commutative_ok : Ok consts_commutative.
Proof using Type.
  step.
  destruct e; trivial.
  destruct n.
  destruct commutative eqn:?; trivial.
  inversion H; clear H; subst.
  epose proof Permutation_partition l isCst.
  eapply Permutation.Permutation_Forall2 in H2; [|eassumption].
  DestructHead.destruct_head'_ex; DestructHead.destruct_head'_and.
  epose proof permute_commutative  _ _ _ _ Heqb H4 _ H0.
  repeat Econstructor; eauto.
  destruct associative eqn:?; [|solve[repeat Econstructor; eauto] ].
  BreakMatch.break_match; [|solve[repeat Econstructor; eauto] ].

  set (fst (partition isCst l)) as csts in *; clearbody csts.
  set (snd (partition isCst l)) as exps in *; clearbody exps.
  clear dependent l. clear dependent args'.
  move o at top; move Heqb0 at top; move Heqb at top.
  eapply eval_interp0_expr in Heqo0; instantiate (1:=d) in Heqo0; instantiate (1:=G) in Heqo0.

  eapply Forall2_app_inv_l in H1; destruct H1 as (?&?&?&?&?); subst.
  rename x0 into xs. rename x1 into ys.
  econstructor. { econstructor. econstructor. econstructor. exact eq_refl. eassumption. }

  inversion Heqo0; clear Heqo0; subst.
  eapply eval_eval_Forall2 in H; eauto; subst.
  clear dependent exps. clear dependent csts.
  clear -H2 H6 Heqb Heqb0.

  change (?x :: ?xs) with ([x] ++ xs).
  rewrite interp_op_associative_app_bind in * by assumption.
  erewrite interp_op_associative_idempotent by eassumption; cbn [Option.bind].
  unfold Option.bind in * |- .
  break_innermost_match_hyps; inversion_option; subst; cbn [Option.bind].
  assumption.
Qed.

Definition neqconst i := fun a : expr => negb (option_beq Z.eqb (interp0_expr a) (Some i)).
Definition drop_identity :=
  fun e => match e with ExprApp (o, args) =>
    match identity o with
    | Some i =>
        let args := List.filter (neqconst i) args in
        match args with
        | nil => ExprApp (const i, nil)
        | _ => ExprApp (o, args)
        end
    | _ => match identity_after_0 o, args with
    | Some i, arg :: args =>
        let args := List.filter (neqconst i) args in
        ExprApp (o, arg :: args)
    | _, _ => e end end | _ => e end.

Lemma filter_neqconst_helper G d id
      l args
      (H : Forall2 (eval G d) l args)
  : exists args',
    Forall2 (eval G d) (filter (neqconst id) l) args'
    /\ List.filter (fun v => negb (Z.eqb v id)) args' = List.filter (fun v => negb (Z.eqb v id)) args.
Proof.
  induction H; cbn; [ eexists; split; constructor | ].
  destruct_head'_ex; destruct_head'_and.
  unfold neqconst at 1.
  unfold negb at 1; break_innermost_match_step; reflect_hyps.
  all: unfold negb at 1; break_innermost_match_step; reflect_hyps.
  all: repeat first [ match goal with
                      | [ H : interp0_expr ?e = Some _, H' : eval ?Gv ?dv ?e _ |- _ ]
                        => apply eval_interp0_expr with (G:=Gv) (d:=dv) in H
                      end
                    | progress reflect_hyps
                    | congruence
                    | progress subst
                    | solve [ eauto ]
                    | step; eauto; [] ].
  all: econstructor; split; [ constructor; eassumption | cbn [filter] ].
  all: unfold negb in *; break_innermost_match; reflect_hyps; try congruence.
Qed.

Lemma filter_neqconst G d o id
      (Hid : identity o = Some id)
      l args
      (H : Forall2 (eval G d) l args)
  : exists args',
    Forall2 (eval G d) (filter (neqconst id) l) args'
    /\ interp_op G o args' = interp_op G o args.
Proof.
  edestruct filter_neqconst_helper as [args' [H1 H2] ]; try eassumption.
  exists args'; split; try eassumption.
  erewrite interp_op_drop_identity, H2, <- interp_op_drop_identity by eassumption.
  reflexivity.
Qed.

Lemma filter_neqconst' G d o id
      (Hid : identity_after_0 o = Some id)
      e arg l args
      (H0 : eval G d e arg)
      (H : Forall2 (eval G d) l args)
  : exists args',
    Forall2 (eval G d) (filter (neqconst id) l) args'
    /\ interp_op G o (arg :: args') = interp_op G o (arg :: args).
Proof.
  edestruct filter_neqconst_helper as [args' [H1 H2] ]; try eassumption.
  exists args'; split; try eassumption.
  erewrite interp_op_drop_identity_after_0, H2, <- interp_op_drop_identity_after_0 by eassumption.
  reflexivity.
Qed.

Global Instance drop_identity_Ok : Ok drop_identity.
Proof using Type.
  repeat (step; eauto; []).
  inversion H; subst; clear H.
  destruct identity eqn:?; [ | destruct identity_after_0 eqn:? ]; break_innermost_match.
  all: repeat (step; eauto; []).
  all: pose proof filter_neqconst.
  all: pose proof filter_neqconst'.
  all: specialize_under_binders_by eassumption.
  all: destruct_head'_ex.
  all: destruct_head'_and.
  all: repeat first [ progress subst
                    | progress inversion_option
                    | match goal with
                      | [ H : ?ls = nil, H' : context[?ls] |- _ ] => rewrite H in H'
                      | [ H : ?ls = cons _ _, H' : context[?ls] |- _ ] => rewrite H in H'
                      | [ H : Forall2 _ nil _ |- _ ] => inversion H; clear H
                      | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                      end
                    | erewrite interp_op_nil_is_identity in * by eassumption
                    | solve [ t ] ].
Qed.

Definition fold_consts_to_and :=
  fun e => match consts_commutative e with
           | ExprApp ((and _ | andZ) as o, ExprApp (const v, nil) :: args)
             => let v' := match o with
                          | and sz => Z.land v (Z.ones (Z.of_N sz))
                          | _ => v
                          end in
                if (v' <? 0)%Z
                then if (v' =? -1)%Z
                     then ExprApp (andZ, args)
                     else ExprApp (andZ, ExprApp (const v', nil) :: args)
                else let v_sz := (1 + Z.log2 v') in
                     if (v' =? Z.ones v_sz)%Z
                     then ExprApp (and (Z.to_N v_sz), args)
                     else ExprApp (and (Z.to_N v_sz), ExprApp (const v', nil) :: args)
           | _ => e
           end.

Global Instance fold_consts_to_and_Ok : Ok fold_consts_to_and.
Proof using Type.
  repeat (step; eauto; []).
  break_innermost_match; try assumption; reflect_hyps.
  all: match goal with
       | [ H : eval _ _ ?e _, H' : consts_commutative ?e = _ |- _ ]
         => apply consts_commutative_ok in H; rewrite H' in H; clear e H'
       end.
  all: repeat (step; eauto; []).
  all: cbn [interp_op fold_right] in *; inversion_option; subst.
  all: repeat first [ match goal with
                      | [ H : Z.land ?x ?y = _ |- context[Z.land (Z.land ?x _) ?y] ]
                        => rewrite !(Z.land_comm x), <- !Z.land_assoc, H
                      | [ |- context[Z.land ?x ?y] ]
                        => match goal with
                           | [ |- context[Z.land ?y ?x] ]
                             => rewrite (Z.land_comm x y)
                           end
                      | [ H : ?x = Z.ones _ |- _ ]
                        => is_var x; rewrite <- H
                      | [ |- Z.land (Z.land ?x ?y) (Z.ones (1 + Z.log2 ?x)) = Z.land ?x ?y ]
                        => rewrite !(Z.land_comm x), <- !Z.land_assoc; f_equal
                      | [ |- Z.land (Z.land (Z.land ?y ?s) ?v) (Z.ones (1 + Z.log2 (Z.land ?y ?s))) = Z.land (Z.land ?y ?v) ?s ]
                        => cut (Z.land (Z.land y s) (Z.ones (1 + Z.log2 (Z.land y s))) = Z.land y s);
                           [ rewrite <- !(Z.land_comm v), <- !Z.land_assoc;
                             let H := fresh in intro H; rewrite H; reflexivity
                           | generalize dependent (Z.land y s); intros ]
                      end
                    | progress autorewrite with zsimplify_const
                    | apply (f_equal (@Some _))
                    | progress cbn [fold_right]
                    | rewrite Z2N.id by auto with zarith
                    | solve [ t ]
                    | solve [ Z.bitblast; now rewrite Z.bits_above_log2 by lia ]
                    | t ].
Qed.

Definition xor_same :=
  fun e => match e with ExprApp (xor _,[x;y]) =>
    if expr_beq x y then ExprApp (const 0, nil) else e | _ => e end.
Global Instance xor_same_ok : Ok xor_same.
Proof using Type.
  t; cbn [fold_right]. rewrite Z.lxor_0_r, Z.lxor_nilpotent; trivial.
Qed.

Definition shift_to_mul :=
  fun e => match e with
    ExprApp ((shl _ | shlZ) as o, [e'; ExprApp (const v, [])]) =>
      let o' := match o with shl bitwidth => mul bitwidth | shlZ => mulZ | _ => o (* impossible *) end in
      let bw := match o with shl bitwidth => Some bitwidth | shlZ => None | _ => None (* impossible *) end in
      if Z.eqb v 0
      then match bw with
           | Some N0 => ExprApp (const 0, nil)
           | Some (Npos p) => ExprApp (slice 0%N (Npos p), [e'])
           | None => e'
           end
      else if Z.ltb 0 v
      then ExprApp (o', [e'; ExprApp (const (2^v)%Z, [])])
      else e | _ => e end.
Global Instance shift_to_mul_ok : Ok shift_to_mul.
Proof. t; cbn in *; rewrite ?Z.shiftl_mul_pow2, ?Z.land_0_r by lia; repeat (lia + f_equal). Qed.

(* o is like mul *)
(* invariant: Forall2 (fun x '(y, z) => eval (o x i) matches eval (o y z)) input output *)
Definition split_consts (o : op) (i : Z) : list expr -> list (expr * Z)
  := List.map
       (fun e
        => match e with
           | ExprApp (o', args)
             => if op_beq o' o
                then
                  let '(csts, exprs) :=
                    if commutative o' && associative o'
                    then let '(csts, exprs) := List.partition isCst args in
                         (interp0_expr (ExprApp (o', csts)), exprs)
                    else
                      (* nest matches for fewer proof cases *)
                      match match args with
                            | [arg; ExprApp ((const c), _)]
                              => Some (c, arg)
                            | _ => None
                            end with
                      | Some (c, arg) => (Some c, [arg])
                      | None => (Some i, args)
                      end
                  in
                  match csts, exprs with
                  | None, _ => (e, i)
                  | Some c, [arg] => (arg, c)
                  | Some c, args => (ExprApp (o', args), c)
                  end
                else (e, i)
           | _ => (e, i)
           end%bool).

(* invariant: input is a permutation of concat (List.map (fun '(e, zs) => List.map (pair e) zs) output) *)
Definition group_consts (ls : list (expr * Z)) : list (expr * list Z)
  := Option.List.map
       (fun xs => match xs with
                  | [] => None
                  | (e, z) :: xs => Some (e, z :: List.map snd xs)
                  end)
       (List.groupAllBy (fun x y => expr_beq (fst x) (fst y)) ls).

(* o is like add *)
(* spec: if interp0_op o zs is always Some _, then Forall2 (fun '(e, zs) '(e', z) => e = e' /\ interp0_op o zs = Some z) input output *)
Definition compress_consts (o : op) (ls : list (expr * list Z)) : list (expr * Z)
  := List.flat_map
       (fun '(e, zs) => match interp0_op o zs with
                        | None => List.map (pair e) zs
                        | Some z => [(e, z)]
                        end)
       ls.

(* o is like mul *)
(* spec is that Forall (fun '(e, z) e' => o (eval e) z matches eval e') inputs outputs *)
Definition app_consts (o : op) (ls : list (expr * Z)) : list expr
  := List.map (fun '(e, z) => let z := ExprApp (const z, []) in
                              let default := ExprApp (o, [e; z]) in
                              if associative o
                              then match e with
                                   | ExprApp (o', args)
                                     => if op_beq o' o
                                        then ExprApp (o, args ++ [z])
                                        else default
                                   | _ => default end else default)
              ls.

Definition combine_consts_pre : expr -> expr :=
  fun e => match e with ExprApp (o, args) =>
    if commutative o && associative o && op_always_interps o then match combines_to o with
    | Some o' => match identity o' with
    | Some idv =>
        ExprApp (o, app_consts o' (compress_consts o (group_consts (split_consts o' idv args))))
    | None => e end | None => e end else e | _ => e end%bool.

Definition cleanup_combine_consts : expr -> expr :=
  let simp_outside := List.fold_left (fun e f => f e) [flatten_associative] in
  let simp_inside := List.fold_left (fun e f => f e) [constprop;drop_identity;unary_truncate;truncate_small] in
  fun e => simp_outside match e with ExprApp (o, args)  =>
    ExprApp (o, List.map simp_inside args)
                   | _ => e end.

Definition combine_consts : expr -> expr := fun e => cleanup_combine_consts (combine_consts_pre e).

Lemma split_consts_correct o i ls G d argsv
      (H : Forall2 (eval G d) ls argsv)
      (Hi : identity o = Some i)
  : Forall2 (fun '(e, z) v => exists v', eval G d e v' /\ (interp_op G o [v'; z] = Some v \/ (z = i /\ (v = v' \/ interp_op G o [v'] = Some v)))) (split_consts o i ls) argsv.
Proof.
  assert (eval G d (ExprApp (o, [])) i) by now econstructor; [ constructor | apply interp_op_nil_is_identity; assumption ].
  cbv [split_consts].
  revert dependent argsv; intro argsv.
  revert argsv; induction ls as [|x xs IH], argsv as [|v argsv];
    try specialize (IH argsv); intros; cbn [List.map];
    invlist Forall2; specialize_by_assumption; constructor; try assumption; clear IH.
  repeat first [ progress inversion_pair
               | progress subst
               | progress inversion_option
               | progress inversion_list
               | progress destruct_head'_ex
               | progress destruct_head'_and
               | progress reflect_hyps
               | rewrite app_nil_r in *
               | solve [ eauto 10 ]
               | eapply ex_intro; split; [ now unshelve (repeat first [ eassumption | econstructor ]) | ]
               | match goal with
                 | [ |- (let '(x, y) := match ?v with _ => _ end in _) _ ]
                   => tryif is_var v then destruct v else destruct v eqn:?
                 | [ H : (match ?v with _ => _ end) = _ |- _ ]
                   => tryif is_var v then destruct v else destruct v eqn:?
                 | [ H : Forall2 _ (_ :: _) _ |- _ ] => rewrite Forall2_cons_l_ex_iff in H
                 | [ H : Forall2 _ [] _ |- _ ] => rewrite Forall2_nil_l_iff in H
                 | [ H : Forall _ (_ :: _) |- _ ] => rewrite Forall_cons_iff in H
                 | [ H : Forall2 _ (_ ++ _) _ |- _ ] => apply Forall2_app_inv_l in H
                 | [ H : interp_op _ (const _) _ = _ |- _ ] => cbn [interp_op] in H
                 | [ H : andb _ _ = true |- _ ] => rewrite Bool.andb_true_iff in H
                 | [ H : ?x = Some _, H' : ?x = Some _ |- _ ] => rewrite H in H'
                 | [ H : context[interp_op _ _ (_ ++ _)] |- _ ] => rewrite interp_op_associative_app_bind in H by assumption; cbv [Crypto.Util.Option.bind] in H
                 | [ H : partition _ _ = _ |- _ ]
                   => let H' := fresh in
                      pose proof H as H'; apply List.Forall_partition in H';
                      let H' := fresh in
                      pose proof H as H'; apply List.partition_eq_filter in H';
                      apply List.partition_permutation in H
                 | [ H : Permutation _ ?l, H' : Forall2 _ ?l ?args, H'' : interp_op _ _ ?args = Some _ |- _ ]
                   => is_var args; eapply Permutation_Forall2 in H'; [ | symmetry; exact H ];
                      let H''' := fresh in
                      destruct H' as [? [H''' H'] ];
                      eapply permute_commutative in H''; try exact H'''; try assumption; [];
                      clear args H'''
                 | [ H : eval _ _ (ExprApp _) _ |- _ ] => inversion H; clear H
                 | [ H : interp0_expr (ExprApp _) = Some _ |- _ ]
                   => eapply eval_interp0_expr in H
                 | [ H : Forall2 (eval _ _) ?ls ?v1, H' : Forall2 (eval _ _) ?ls ?v2 |- _ ]
                   => assert (v1 = v2) by (eapply eval_eval_Forall2; eassumption);
                      clear H'
                 | [ H : Permutation (@filter ?A ?f ?ls) ?ls |- _ ]
                   => apply Permutation_length, List.filter_eq_length_eq in H;
                      generalize dependent (@filter A f ls); intros; subst
                 | [ H : interp_op _ ?o [?x] = Some _ |- context[interp_op _ ?o (?x :: ?ls)] ]
                   => change (x :: ls) with ([x] ++ ls);
                      rewrite interp_op_associative_app_bind, H by assumption;
                      try erewrite interp_op_associative_idempotent by eassumption;
                      cbn [Crypto.Util.Option.bind]
                 | [ H : commutative ?o = true, H' : interp_op _ ?o [?a; ?b] = Some ?v |- interp_op _ ?o [?b; ?a] = Some ?v \/ _ ]
                   => left; erewrite permute_commutative; [ reflexivity | .. ]; try eassumption; rewrite Permutation_rev; reflexivity
                 end
               | erewrite <- interp_op_associative_app by eassumption ].
Qed.

Lemma group_consts_Permutation ls
  : Permutation (List.concat (List.map (fun '(e, zs) => List.map (pair e) zs) (group_consts ls))) ls.
Proof.
  cbv [group_consts].
  let fv := match goal with |- context[List.groupAllBy ?f ls] => f end in
  pose proof (@List.Forall_groupAllBy _ fv ls) as H;
  etransitivity; [ | apply List.concat_groupAllBy with (f:=fv) ];
  generalize dependent (List.groupAllBy fv ls); intro gfls; intros.
  match goal with |- ?R ?x ?y => cut (x = y); [ intros ->; reflexivity | ] end.
  apply f_equal.
  induction H; [ reflexivity | ]; cbn.
  break_innermost_match; cbn [List.map]; try solve [ exfalso; assumption ].
  repeat (f_equal; try assumption; []).
  cbn [fst snd] in *.
  lazymatch goal with
  | [ H : Forall _ ?ls |- map (pair _) (map snd ?ls) = ?ls ]
    => revert H; clear
  end.
  intro H; induction H; destruct_head'_prod; cbn [List.map fst snd]; reflect_hyps; subst; cbn [fst snd].
  all: f_equal; assumption.
Qed.

Lemma group_consts_nonempty ls
  : Forall (fun '(e, zs) => zs <> nil) (group_consts ls).
Proof.
  cbv [group_consts].
  let fv := match goal with |- context[List.groupAllBy ?f ls] => f end in
  pose proof (@List.Forall_groupAllBy_full _ fv ls) as H;
  generalize dependent (List.groupAllBy fv ls); intro gfls; intros.
  induction gfls as [|x xs IH]; cbn [list_rect Option.List.map fold_right] in *; break_innermost_match; destruct_head'_and; destruct_head'_False;
    constructor; try congruence; eauto.
Qed.

Lemma compress_consts_correct o ls
      (Ho : op_always_interps o = true)
  : Forall2 (fun '(e, zs) '(e', z) => e = e' /\ interp0_op o zs = Some z) ls (compress_consts o ls).
Proof.
  cbv [compress_consts].
  induction ls as [|x xs IH]; cbn [List.flat_map]; break_innermost_match; cbn [List.app];
    try solve [ exfalso; eapply interp0_op_always_interps; eassumption ]; constructor; eauto.
Qed.

(* in a more specific, usable form *)
Lemma compress_consts_correct_alt G d o' o ls argsv
      (Ho : op_always_interps o = true)
      (H : Forall2 (fun '(e, zs) v => exists z, interp0_op o zs = Some z /\ exists v', (exists xs, interp_op G o' xs = Some z) /\ eval G d e v' /\ interp_op G o' [v'; z] = Some v) ls argsv)
  : Forall2 (fun '(e, z) v => exists v', (exists xs, interp_op G o' xs = Some z) /\ eval G d e v' /\ interp_op G o' [v'; z] = Some v) (compress_consts o ls) argsv.
Proof.
  eapply compress_consts_correct in Ho.
  apply Forall2_flip in H.
  eapply Forall2_trans in Ho; [ | exact H ].
  apply Forall2_flip.
  eapply Forall2_weaken; [ | eassumption ]; cbv beta.
  intros; repeat (destruct_head'_ex || destruct_head'_prod || destruct_head'_and || subst).
  repeat first [ progress inversion_option
               | progress subst
               | match goal with
                 | [ H : ?x = Some _, H' : ?x = Some _ |- _ ] => rewrite H in H'
                 end
               | solve [ eauto ] ].
Qed.

Lemma app_consts_correct G d o ls argsv
      (H : Forall2 (fun '(e, z) v => exists v', (exists xs, interp_op G o xs = Some z) /\ eval G d e v' /\ interp_op G o [v'; z] = Some v) ls argsv)
  : Forall2 (eval G d) (app_consts o ls) argsv.
Proof.
  cbv [app_consts].
  induction H; cbn [List.map]; constructor.
  all: repeat first [ assumption
                    | progress destruct_head'_prod
                    | progress destruct_head'_ex
                    | progress destruct_head'_and
                    | progress subst
                    | progress reflect_hyps
                    | break_innermost_match_step
                    | match goal with
                      | [ |- eval _ _ (ExprApp (_, [_; _])) _ ]
                        => econstructor; [ | eassumption ]; unshelve (repeat (constructor; [ shelve | ])); [ .. | constructor ]
                      | [ |- eval _ _ (ExprApp (const ?z, [])) _ ]
                        => econstructor; [ constructor | reflexivity ]
                      end
                    | step; eauto; []
                    | match goal with
                      | [ |- eval _ _ (ExprApp (_, _ ++ _)) _ ]
                        => econstructor; [ repeat first [ eassumption | apply Forall2_app | apply Forall2_cons | apply Forall2_nil ] | ]
                      end
                    | erewrite interp_op_associative_app; try eassumption; []
                    | eapply interp_op_associative_idempotent; try eassumption ].
Qed.

Lemma combines_to_correct o o' v G xs vxs xsv
      (H : combines_to o = Some o')
      (H' : Forall2 (fun x vx => interp_op G o' [v; x] = Some vx) xs vxs)
      (H'' : interp_op G o xs = Some xsv)
  : interp_op G o' [v; xsv] = interp_op G o vxs.
Proof.
  cbv [combines_to] in H; destruct o; inversion_option; subst.
  all: cbn [interp_op fold_right] in *; inversion_option; subst; apply f_equal.
  all: autorewrite with zsimplify_const in *.
  all: rewrite ?Z.land_ones by lia; push_Zmod; pull_Zmod.
  all: eapply Forall2_weaken in H';
    [
    | intros *;
      let H := fresh in
      intro H;
      inversion_option;
      autorewrite with zsimplify_const in H;
      rewrite ?Z.land_ones in H by lia; exact H ].
  all: rewrite <- Forall2_map_l in H'.
  all: apply Forall2_eq in H'; subst.
  all: induction xs as [|x xs IH]; cbn [fold_right List.map]; autorewrite with zsimplify_const; try reflexivity.
  all: push_Zmod; pull_Zmod.
  all: revert IH; push_Zmod; intro IH; rewrite <- IH; clear IH; pull_Zmod.
  all: rewrite <- Z.mul_add_distr_l.
  all: reflexivity.
Qed.

(* should this be factored differently? *)
Lemma interp_op_combines_to_idempotent G o o' (H : combines_to o = Some o') xs vxs
  : interp_op G o xs = Some vxs -> interp_op G o' [vxs] = Some vxs.
Proof.
  destruct o; cbv [combines_to] in *; inversion_option; subst; cbn [interp_op fold_right]; intros; inversion_option; subst.
  all: autorewrite with zsimplify_const.
  all: apply f_equal; try reflexivity.
  rewrite ?Z.land_ones by lia; push_Zmod; pull_Zmod.
  reflexivity.
Qed.

Lemma interp_op_combines_to_idempotent_rev G o o' (H : combines_to o = Some o') xs vxs
  : interp_op G o' xs = Some vxs -> interp_op G o [vxs] = Some vxs.
Proof.
  destruct o; cbv [combines_to] in *; inversion_option; subst; cbn [interp_op fold_right]; intros; inversion_option; subst.
  all: autorewrite with zsimplify_const.
  all: apply f_equal; try reflexivity.
  rewrite ?Z.land_ones by lia; push_Zmod; pull_Zmod.
  reflexivity.
Qed.

Lemma interp_op_combines_to_singleton_same_size G o o' (H : combines_to o = Some o') v
  : interp_op G o [v] = interp_op G o' [v].
Proof.
  destruct o; cbv [combines_to] in *; inversion_option; subst; cbn [interp_op fold_right]; intros; inversion_option; subst.
  all: autorewrite with zsimplify_const.
  all: reflexivity.
Qed.

(* a more general version useful for us *)
Lemma combines_to_correct_or o o' v G xs vxs xsv
      (Ho : associative o = true)
      (Ho' : op_always_interps o = true)
      (H : combines_to o = Some o')
      (H' : Forall2 (fun x vx => interp_op G o' [v; x] = Some vx \/ interp_op G o' [v; x] = interp_op G o' [vx]) xs vxs)
      (H'' : interp_op G o xs = Some xsv)
  : interp_op G o' [v; xsv] = interp_op G o vxs.
Proof.
  rewrite <- (List.concat_map_singleton vxs).
  rewrite interp_op_associative_spec_concat, map_map by assumption.
  rewrite Option.List.bind_list_cps_id, <- Option.List.eq_bind_list_lift; cbv [Crypto.Util.Option.bind]; break_match; revgoals.
  { exfalso.
    let H := match goal with H : _ = None |- _ => H end in
    revert H; clear -Ho Ho'.
    cbv [Option.List.lift].
    induction vxs as [|?? IH]; cbn; cbv [Crypto.Util.Option.bind] in *; break_match; try congruence.
    intro; eapply interp_op_always_interps; eassumption. }
  eapply combines_to_correct; try eassumption.
  let l := match goal with |- Forall2 _ _ ?l => l end in
  revert dependent xsv; revert dependent l.
  cbv [Option.List.lift] in *.
  induction H'; cbn [List.map fold_right]; intros [|z xs]; intros; cbv [Crypto.Util.Option.bind] in *; break_match_hyps.
  all: inversion_option; inversion_list; subst; constructor.
  all: repeat first [ break_innermost_match_hyps_step
                    | progress inversion_option
                    | progress subst
                    | assumption
                    | match goal with
                      | [ H : forall x, Some _ = Some x -> _ |- _ ] => specialize (H _ eq_refl)
                      | [ H : context[?x :: ?l] |- _ ]
                        => is_var x; is_var l; change (x :: l) with ([x] ++ l) in *;
                           rewrite interp_op_associative_app_bind in H by assumption;
                           cbv [Crypto.Util.Option.bind] in H
                      | [ H : context[interp_op _ _ [_] ] |- _ ] => erewrite interp_op_combines_to_idempotent_rev in H by eassumption
                      end
                    | progress destruct_head'_or
                    | erewrite interp_op_combines_to_singleton_same_size in * by eassumption
                    | congruence ].
Qed.

Lemma combines_to_correct_alt G d o o' xs ys i z z1 e
      (Ho : combines_to o = Some o')
      (Hi : identity o' = Some i)
      (Ha : associative o = true)
      (Hai : op_always_interps o = true)
      (H : Forall2 (fun x y => exists v', eval G d e v' /\ (interp_op G o' [v'; x] = Some y \/ (x = i /\ (y = v' \/ interp_op G o' [v'] = Some y)))) xs ys)
      (H' : interp_op G o ys = Some z1)
      (Hz : interp_op G o xs = Some z)
      (Hnonempty : xs <> nil)
  : exists v' : Z, (exists xs0 : list Z, interp_op G o' xs0 = Some z) /\ eval G d e v' /\ interp_op G o' [v'; z] = Some z1.
Proof.
  cut (exists v', eval G d e v');
    [ intros [ev ?]; exists ev
    | match goal with
      | [ H : Forall2 _ ?l _, H' : ?l <> [] |- _ ]
        => inversion H; subst; try congruence; destruct_head'_ex; destruct_head'_and; eauto
      end ].
  repeat apply conj.
  { eexists [_]; eapply interp_op_combines_to_idempotent; eassumption. }
  { assumption. }
  { rewrite <- H'.
    eapply combines_to_correct_or; try eassumption.
    clear z1 z H' Hz Hnonempty.
    induction H; constructor; eauto.
    repeat (destruct_head'_ex; destruct_head'_and; destruct_head'_or).
    all: repeat (step; eauto; []); subst; eauto.
    all: erewrite @interp_op_drop_identity in * by eassumption; cbn [filter] in *; cbv [negb] in *; break_innermost_match; break_innermost_match_hyps;
      reflect_hyps; subst.
    all: try congruence.
    all: try now (idtac + left); apply interp_op_nil_is_identity.
    all: eauto. }
Qed.

Lemma combine_consts_helper o o' G d ls args i
      (H : Forall2
             (fun '(e, zs) y =>
                Forall2
                  (fun '(e, z') (v : Z) =>
                     exists v' : Z, eval G d e v' /\ (interp_op G o' [v'; z'] = Some v \/ (z' = i /\ (v = v' \/ interp_op G o' [v'] = Some v))))
                  (map (pair e) zs) y)
             ls args)
      (Hi' : identity o' = Some i)
      (Halways : op_always_interps o = true)
      (Hassoc : associative o = true)
      (Hc : combines_to o = Some o')
      (Hnonempty : Forall (fun '(e, zs) => zs <> nil) ls)
  : exists args',
    interp_op G o (concat args) = interp_op G o args'
    /\ Forall2
         (fun '(e, zs) (v0 : Z) =>
            exists z' : Z,
              interp0_op o zs = Some z' /\
                (exists v' : Z, (exists xs : list Z, interp_op G o' xs = Some z') /\ eval G d e v' /\ interp_op G o' [v'; z'] = Some v0))
         ls args'.
Proof.
  revert ls args H Hnonempty.
  induction ls as [|x xs IH], args as [|arg args]; try specialize (IH args).
  all: rewrite ?Forall2_nil_l_iff, ?Forall2_nil_r_iff, ?Forall2_cons_cons_iff; try congruence.
  { exists nil; split; [ cbn; reflexivity | constructor ]. }
  repeat first [ progress destruct_head_prod
               | progress destruct_head_and
               | progress destruct_head_ex
               | progress intros
               | progress specialize_by_assumption
               | progress invlist Forall ].
  match goal with
  | [ |- ex ?P ] => cut (exists a b, P ([a] ++ b)); [ intros [a [b ?] ]; exists ([a] ++ b); assumption | ]
  end.
  cbv beta.
  rewrite !interp_op_associative_app_bind by assumption.
  setoid_rewrite interp_op_associative_app_bind; [ | assumption ].
  cbv [Crypto.Util.Option.bind]; break_innermost_match; inversion_option; subst; do 2 eexists; break_innermost_match; split; try reflexivity.
  all: repeat first [ progress inversion_option
                    | match goal with
                      | [ H : interp_op _ _ ?l = Some ?x, H' : interp_op _ _ [?v] = Some ?x' |- interp_op _ _ [?x; ?y] = interp_op _ _ [?x'; ?y'] ]
                        => erewrite interp_op_associative_idempotent in H' by first [ exact H | assumption ]
                      | [ H : Some _ = _ |- _ ] => symmetry in H
                      | [ H : interp_op _ _ [?x] = _ |- _ ]
                        => tryif is_evar x then fail else erewrite interp_op_associative_idempotent in H by eassumption
                      | [ H : interp_op _ _ _ = None |- _ ]
                        => apply interp_op_always_interps in H; [ exfalso | assumption ]
                      end
                    | progress subst
                    | progress cbn [List.app]
                    | apply Forall2_cons
                    | eassumption
                    | rewrite @Forall2_map_l_iff in *
                    | match goal with
                      | [ |- exists z, interp0_op ?o ?l = Some z /\ _ ]
                        => let H := fresh in
                           destruct (interp0_op o l) eqn:H;
                           [ eexists; split; [ reflexivity | ]
                           | apply interp_op_always_interps in H; [ exfalso | assumption ] ]
                      end ].
  all: try congruence.
  eapply combines_to_correct_alt; try ((idtac + eapply interp_op_interp0_op); eassumption).
  Unshelve.
  all: try solve [ constructor ].
Qed.

Global Instance cleanup_combine_consts_Ok : Ok cleanup_combine_consts.
Proof.
  repeat (step; eauto; []); cbn [fold_left].
  repeat match goal with
         | [ |- eval _ _ (?r ?e) _ ]
           => apply (_:Ok r)
         end.
  econstructor; [ | eassumption ].
  rewrite Forall2_map_l.
  rewrite !@Forall2_forall_iff_nth_error in *; cbv [option_eq] in *.
  intros.
  repeat match goal with
         | [ H : context[nth_error ?l] |- context[nth_error ?l ?i] ] => specialize (H i)
         end.
  break_innermost_match; eauto.
  cbn [fold_left].
  repeat lazymatch goal with
  | H : eval ?c ?d ?e _ |- context[?r ?e] =>
    let Hr := fresh in epose proof ((_:Ok r) _ _ _ _ H) as Hr; clear H
  end.
  assumption.
Qed.

Global Instance combine_consts_pre_Ok : Ok combine_consts_pre.
Proof using Type.
  repeat (step; eauto; []).
  match goal with
  | [ |- context[split_consts ?o ?i ?l] ]
    => pose proof (@split_consts_correct o i l _ _ _ ltac:(eassumption) ltac:(assumption)) as Hs
  end.
  match goal with
  | [ |- context[group_consts ?ls] ]
    => pose proof (@group_consts_Permutation ls) as Hg;
       pose proof (@group_consts_nonempty ls) as Hg'
  end.
  eapply Permutation_Forall2 in Hs; [ | symmetry; exact Hg ].
  destruct Hs as [? [? Hs] ].
  let H := match goal with H : interp_op _ _ _ = Some _ |- _ => H end in
  eapply permute_commutative in H; [ | eassumption .. ].
  rewrite Forall2_concat_l_ex_iff in Hs.
  destruct Hs as [? [? Hs] ]; subst.
  rewrite Forall2_map_l_iff in Hs.
  eapply Forall2_weaken, combine_consts_helper in Hs; try assumption; try solve [ intros; destruct_head'_prod; eassumption ]; [ | try eassumption .. ].
  destruct Hs as [? [? Hs] ].
  econstructor; [ apply app_consts_correct, compress_consts_correct_alt; try assumption | ].
  { eassumption. }
  { congruence. }
Qed.

Global Instance combine_consts_Ok : Ok combine_consts.
Proof. repeat step; apply cleanup_combine_consts_Ok, combine_consts_pre_Ok; assumption. Qed.

Definition expr : expr -> expr :=
  List.fold_left (fun e f => f e)
  [constprop
  ;slice0
  ;slice01_addcarryZ
  ;slice01_subborrowZ
  ;set_slice_set_slice
  ;slice_set_slice
  ;set_slice0_small
  ;shift_to_mul
  ;flatten_associative
  ;consts_commutative
  ;fold_consts_to_and
  ;drop_identity
  ;unary_truncate
  ;truncate_small
  ;combine_consts
  ;addoverflow_bit
  ;addcarry_bit
  ;addcarry_small
  ;addoverflow_small
  ;addbyte_small
  ;xor_same
  ].

Lemma eval_expr c d e v : eval c d e v -> eval c d (expr e) v.
Proof using Type.
  intros H; cbv [expr fold_left].
  repeat lazymatch goal with
  | H : eval ?c ?d ?e _ |- context[?r ?e] =>
    let Hr := fresh in epose proof ((_:Ok r) _ _ _ _ H) as Hr; clear H
  end.
  eassumption.
Qed.
End Rewrite.

Definition simplify (dag : dag) (e : node idx) :=
  Rewrite.expr (reveal_node_at_least dag 3 e).

Lemma eval_simplify G d n v : eval_node G d n v -> eval G d (simplify d n) v.
Proof using Type. eauto using Rewrite.eval_expr, eval_node_reveal_node_at_least. Qed.

Definition reg_state := Tuple.tuple (option idx) 16.
Definition flag_state := Tuple.tuple (option idx) 6.
Definition mem_state := list (idx * idx).

Definition get_flag (st : flag_state) (f : FLAG) : option idx
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     match f with
     | CF => cfv
     | PF => pfv
     | AF => afv
     | ZF => zfv
     | SF => sfv
     | OF => ofv
     end.
Definition set_flag_internal (st : flag_state) (f : FLAG) (v : option idx) : flag_state
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     (match f with CF => v | _ => cfv end,
      match f with PF => v | _ => pfv end,
      match f with AF => v | _ => afv end,
      match f with ZF => v | _ => zfv end,
      match f with SF => v | _ => sfv end,
      match f with OF => v | _ => ofv end).
Definition set_flag (st : flag_state) (f : FLAG) (v : idx) : flag_state
  := set_flag_internal st f (Some v).
Definition havoc_flag (st : flag_state) (f : FLAG) : flag_state
  := set_flag_internal st f None.
Definition havoc_flags : flag_state
  := (None, None, None, None, None, None).
Definition reverse_lookup_flag (st : flag_state) (i : idx) : option FLAG
  := option_map
       (@snd _ _)
       (List.find (fun v => option_beq N.eqb (Some i) (fst v))
                  (Tuple.to_list _ (Tuple.map2 (@pair _ _) st (CF, PF, AF, ZF, SF, OF)))).

Definition get_reg (st : reg_state) (ri : nat) : option idx
  := Tuple.nth_default None ri st.
Definition set_reg (st : reg_state) ri (i : idx) : reg_state
  := Tuple.from_list_default None _ (ListUtil.set_nth
       ri
       (Some i)
       (Tuple.to_list _ st)).
Definition reverse_lookup_widest_reg (st : reg_state) (i : idx) : option REG
  := option_map
       (fun v => widest_register_of_index (fst v))
       (List.find (fun v => option_beq N.eqb (Some i) (snd v))
                  (List.enumerate (Tuple.to_list _ st))).

Definition load (a : idx) (s : mem_state) : option idx :=
  option_map snd (find (fun p => fst p =? a)%N s).
Definition remove (a : idx) (s : mem_state) : list idx * mem_state :=
  let '(vs, s) := List.partition (fun p => fst p =? a)%N s in
  (List.map snd vs, s).
Definition store (a v : idx) (s : mem_state) : option mem_state :=
  n <- indexof (fun p => fst p =? a)%N s;
  Some (ListUtil.update_nth n (fun ptsto => (fst ptsto, v)) s).
Definition reverse_lookup_mem (st : mem_state) (i : idx) : option (N * idx)
  := option_map
       (fun '(n, (_, ptsto)) => (N.of_nat n, ptsto))
       (List.find (fun v => N.eqb i (fst (snd v)))
                  (List.enumerate st)).

Local Unset Boolean Equality Schemes.
Local Unset Decidable Equality Schemes.
Record symbolic_state := { dag_state :> dag ; symbolic_reg_state :> reg_state ; symbolic_flag_state :> flag_state ; symbolic_mem_state :> mem_state }.
Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.

Definition update_dag_with (st : symbolic_state) (f : dag -> dag) : symbolic_state
  := {| dag_state := f st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_reg_with (st : symbolic_state) (f : reg_state -> reg_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := f st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_flag_with (st : symbolic_state) (f : flag_state -> flag_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := f st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_mem_with (st : symbolic_state) (f : mem_state -> mem_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := f st.(symbolic_mem_state) |}.

Global Instance show_reg_state : Show reg_state := fun st =>
  show (List.map (fun '(n, v) => (widest_register_of_index n, v)) (ListUtil.List.enumerate (Option.List.map id (Tuple.to_list _ st)))).

Global Instance show_flag_state : Show flag_state :=
  fun '(cfv, pfv, afv, zfv, sfv, ofv) => (
  "(*flag_state*)(CF="++show cfv
  ++" PF="++show pfv
  ++" AF="++show afv
  ++" ZF="++show zfv
  ++" SF="++show sfv
  ++" ZF="++show zfv
  ++" OF="++show ofv++")")%string.

Print dag.t.
Print node.
Print expr.
Print dag.lookup.
Print bound_expr.

Print reveal.

Fixpoint bound_expr' e : option Z := (* e <= r *)
  match e with
  | ExprApp (const v, _) => if Z.leb 0 v then Some v else None
  | ExprApp (add s, args) =>
      Some  match Option.List.lift (List.map bound_expr' args) with
            | Some bounds => Z.min (List.fold_right Z.add 0%Z bounds) (Z.ones (Z.of_N s))
            | None => Z.ones (Z.of_N s)
            end
  | ExprApp (selectznz, [c;a;b]) =>
      match bound_expr' a, bound_expr' b with
      | Some a, Some b => Some (Z.max a b)
      | _, _ => None
      end
  | ExprApp (set_slice 0 w, [a;b]) =>
      match bound_expr' a, bound_expr' b with
      | Some a, Some b => Some (Z.lor
                                  (Z.land (Z.ones (Z.succ (Z.log2 b))) (Z.ones (Z.of_N w)))
                                  (Z.ldiff (Z.ones (Z.succ (Z.log2 a))) (Z.ones (Z.of_N w))))
      | _, _ => None
      end
  | ExprApp ((old s _ | slice _ s | mul s | shl s | shr s | sar s | neg s | and s | or s | xor s), _) => Some (Z.ones (Z.of_N s))
  | ExprApp ((addcarry _ | subborrow _ | addoverflow _ | iszero), _) => Some 1
  | _ => None
  end%Z.



Global Instance show_lines_dag : ShowLines dag := (fun d:dag =>
  ["(*dag*)["]
    ++List.map (fun '(i, v, descr) =>"(*"++show i ++"*) " ++ show v++";"++ show (bound_expr (reveal d 1000 i))
                                         ++ (if dag.get_eager_description_always_show descr
                                             then match dag.get_eager_description_description descr with
                                                  | Some descr => " " ++ String.Tab ++ "(*" ++ descr ++ "*)"
                                                  | None => ""
                                                  end
                                             else ""))%string (dag.eager.force d)
  ++["]"])%list%string.
Global Instance show_lines_mem_state : ShowLines mem_state :=
  @show_lines_list _ ShowLines_of_Show.

Global Instance ShowLines_symbolic_state : ShowLines symbolic_state :=
 fun X : symbolic_state =>
 match X with
 | {|
     dag_state := ds;
     symbolic_reg_state := rs;
     symbolic_flag_state := fs;
     symbolic_mem_state := ms
   |} =>
   ["(*symbolic_state*) {|";
   "  dag_state :="] ++ show_lines ds ++ [";";
   ("  symbolic_reg_state := " ++ show rs ++ ";")%string;
   ("  symbolic_flag_state := " ++ show fs ++";")%string;
   "  symbolic_mem_state :="] ++show_lines ms ++ [";";
   "|}"]
 end%list%string.


Module error.
  Local Unset Boolean Equality Schemes.
  Local Unset Decidable Equality Schemes.
  Variant error :=
  | get_flag (f : FLAG) (s : flag_state)
  | get_reg (r : nat + REG) (s : reg_state)
  | load (a : idx) (s : symbolic_state)
  | remove (a : idx) (s : symbolic_state)
  | remove_has_duplicates (a : idx) (vs : list idx) (s : symbolic_state)
  | store (a v : idx) (s : symbolic_state)
  | set_const (_ : CONST) (_ : idx)
  | expected_const (_ : idx) (_ : expr)

  | unsupported_memory_access_size (_:N)
  | unsupported_label_in_memory (_:string)
  | unsupported_label_argument (_:JUMP_LABEL)
  | unimplemented_prefix (_:NormalInstruction)
  | unimplemented_instruction (_ : NormalInstruction)
  | unsupported_line (_ : RawLine)
  | ambiguous_operation_size (_ : NormalInstruction)
  .

  Global Instance show_lines_error : ShowLines error
    := fun e
       => match e with
          | get_flag f s
            => ["In flag state " ++ show_flag_state s;
                "Flag " ++ show f ++ " was read without being set."]
          | get_reg (inl i) s
            => ["Invalid reg index " ++ show_nat i]
          | get_reg (inr r) s
            => ["In reg state " ++ show_reg_state s;
                "Register " ++ show (r : REG) ++ " read without being set."]
          | load a s
            => (["In mem state:"]
                  ++ show_lines_mem_state s
                  ++ ["Index " ++ show a ++ " loaded without being present."]%string)%list
          | remove a s
            => (["In mem state:"]
                  ++ show_lines_mem_state s
                  ++ ["Index " ++ show a ++ " removed without being present."]%string)%list
          | remove_has_duplicates a ls s
            => (["In mem state:"]
                  ++ show_lines_mem_state s
                  ++ ["Index " ++ show a ++ " occurs multiple times during removal (" ++ show ls ++ ")."]%string)%list
          | store a v s
            => (["In mem state:"]
                  ++ show_lines_mem_state s
                  ++ ["Index " ++ show a ++ " updated (with value " ++ show v ++ ") without being present."]%string)%list
          | set_const c i
            => ["SetOperand called with Syntax.const " ++ show c ++ " " ++ show i]%string
          | expected_const i x
            => ["RevealConst called at " ++ show i ++ " resulted in non-const value " ++ show x]
          | unsupported_memory_access_size n => ["error.unsupported_memory_access_size " ++ show n]
          | unsupported_label_in_memory l => ["error.unsupported_label_in_memory " ++ l]
          | unsupported_label_argument l => ["error.unsupported_label_argument " ++ show l]
          | unimplemented_instruction n => ["error.unimplemented_instruction " ++ show n]
          | unimplemented_prefix n => ["error.unimplemented_prefix " ++ show n]
          | unsupported_line n => ["error.unsupported_line " ++ show n]
          | ambiguous_operation_size n => ["error.ambiguous_operation_size " ++ show n]
          end%string.
  Global Instance Show_error : Show error := _.
End error.
Notation error := error.error.

Definition M T := symbolic_state -> ErrorT (error * symbolic_state) (T * symbolic_state).
Definition ret {A} (x : A) : M A :=
  fun s => Success (x, s).
Definition err {A} (e : error) : M A :=
  fun s => Error (e, s).
Definition some_or {A} (f : symbolic_state -> option A) (e : symbolic_state -> error) : M A :=
  fun st => match f st with Some x => Success (x, st) | None => Error (e st, st) end.
Definition bind {A B} (x : M A) (f : A -> M B) : M B :=
  fun s => (x_s <- x s; f (fst x_s) (snd x_s))%error.
Definition lift_dag {A} (v : dag.M A) : M A :=
  fun s => let '(v, d) := v s.(dag_state) in
           Success (v, update_dag_with s (fun _ => d)).

Declare Scope x86symex_scope.
Delimit Scope x86symex_scope with x86symex.
Bind Scope x86symex_scope with M.
Notation "x <- y ; f" := (bind y (fun x => f%x86symex)) : x86symex_scope.
Section MapM. (* map over a list in the state monad *)
  Context {A B} (f : A -> M B).
  Fixpoint mapM (l : list A) : M (list B) :=
    match l with
    | nil => ret nil
    | cons a l => b <- f a; bs <- mapM l; ret (cons b bs)
    end%x86symex.
End MapM.
Definition mapM_ {A B} (f: A -> M B) l : M unit := _ <- mapM f l; ret tt.

Definition error_get_reg_of_reg_index ri : symbolic_state -> error
  := error.get_reg (let r := widest_register_of_index ri in
                    if (reg_index r =? ri)%nat
                    then inr r
                    else inl ri).

Definition GetFlag f : M idx :=
  some_or (fun s => get_flag s f) (error.get_flag f).
Definition GetReg64 ri : M idx :=
  some_or (fun st => get_reg st ri) (error_get_reg_of_reg_index ri).
Definition Load64 (a : idx) : M idx := some_or (load a) (error.load a).
Definition Remove64 (a : idx) : M idx
  := fun s => let '(vs, m) := remove a s in
              match vs with
              | [] => Error (error.remove a s, s)
              | [v] => Success (v, update_mem_with s (fun _ => m))
              | vs => Error (error.remove_has_duplicates a vs s, s)
              end.
Definition SetFlag f i : M unit :=
  fun s => Success (tt, update_flag_with s (fun s => set_flag s f i)).
Definition HavocFlags : M unit :=
  fun s => Success (tt, update_flag_with s (fun _ => Tuple.repeat None 6)).
Definition PreserveFlag {T} (f : FLAG) (k : M T) : M T :=
  vf <- (fun s => Success (get_flag s f, s));
  x <- k;
  _ <- (fun s => Success (tt, update_flag_with s (fun s => set_flag_internal s f vf)));
  ret x.
Definition SetReg64 rn i : M unit :=
  fun s => Success (tt, update_reg_with s (fun s => set_reg s rn i)).
Definition Store64 (a v : idx) : M unit :=
  ms <- some_or (store a v) (error.store a v);
  fun s => Success (tt, update_mem_with s (fun _ => ms)).
Definition Merge {descr : description} (e : expr) : M idx := fun s =>
  let i_dag := merge e s in
  Success (fst i_dag, update_dag_with s (fun _ => snd i_dag)).
Definition App {descr : description} (n : node idx) : M idx :=
  fun s => Merge (simplify s n) s.
Definition Reveal n (i : idx) : M expr :=
  fun s => Success (reveal s n i, s).
Definition RevealConst (i : idx) : M Z :=
  x <- Reveal 1 i;
  match x with
  | ExprApp (const n, nil) => ret n
  | _ => err (error.expected_const i x)
  end.

Definition GetReg {descr:description} r : M idx :=
  let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg r in
  v <- GetReg64 rn;
  App ((slice lo sz), [v]).
Definition SetReg {descr:description} r (v : idx) : M unit :=
  let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg r in
  if N.eqb sz 64
  then v <- App (slice 0 64, [v]);
       SetReg64 rn v (* works even if old value is unspecified *)
  else old <- GetReg64 rn;
       v <- App ((set_slice lo sz), [old; v]);
       SetReg64 rn v.

Class AddressSize := address_size : OperationSize.
Definition Address {descr:description} {sa : AddressSize} (a : MEM) : M idx :=
  _ <- match a.(mem_base_label) with
       | None => ret tt
       | Some l => err (error.unsupported_label_in_memory l)
       end;
  base <- match a.(mem_base_reg) with
           | Some r => GetReg r
           | None => App ((const 0), nil)
           end;
  index <- match a.(mem_scale_reg) with
           | Some (z, r) => z <- App (zconst sa z, []); r <- GetReg r; App (mul sa, [r; z])
           | None => App ((const 0), nil)
           end;
  offset <- App (match a.(mem_offset) with
                             | Some s => (zconst sa s, nil)
                             | None => (const 0, nil) end);
  bi <- App (add sa, [base; index]);
  App (add sa, [bi; offset]).

Definition Load {descr:description} {s : OperationSize} {sa : AddressSize} (a : MEM) : M idx :=
  if negb (orb (Syntax.operand_size a s =? 8 )( Syntax.operand_size a s =? 64))%N
  then err (error.unsupported_memory_access_size (Syntax.operand_size a s)) else
  addr <- Address a;
  v <- Load64 addr;
  App ((slice 0 (Syntax.operand_size a s)), [v]).

Definition Remove {descr:description} {s : OperationSize} {sa : AddressSize} (a : MEM) : M idx :=
  if negb (orb (Syntax.operand_size a s =? 8 )( Syntax.operand_size a s =? 64))%N
  then err (error.unsupported_memory_access_size (Syntax.operand_size a s)) else
  addr <- Address a;
  v <- Remove64 addr;
  App ((slice 0 (Syntax.operand_size a s)), [v]).

Definition Store {descr:description} {s : OperationSize} {sa : AddressSize} (a : MEM) v : M unit :=
  if negb (orb (Syntax.operand_size a s =? 8 )( Syntax.operand_size a s =? 64))%N
  then err (error.unsupported_memory_access_size (Syntax.operand_size a s)) else
  addr <- Address a;
  old <- Load64 addr;
  v <- App (slice 0 (Syntax.operand_size a s), [v]);
  v <- App (set_slice 0 (Syntax.operand_size a s), [old; v])%N;
  Store64 addr v.

(* note: this could totally just handle truncation of constants if semanics handled it *)
Definition GetOperand {descr:description} {s : OperationSize} {sa : AddressSize} (o : ARG) : M idx :=
  match o with
  | Syntax.const a => App (zconst s a, [])
  | mem a => Load a
  | reg r => GetReg r
  | label l => err (error.unsupported_label_argument l)
  end.

Definition SetOperand {descr:description} {s : OperationSize} {sa : AddressSize} (o : ARG) (v : idx) : M unit :=
  match o with
  | Syntax.const a => err (error.set_const a v)
  | mem a => Store a v
  | reg a => SetReg a v
  | label l => err (error.unsupported_label_argument l)
  end.

Local Unset Elimination Schemes.
Inductive pre_expr : Set :=
| PreARG (_ : ARG)
| PreFLG (_ : FLAG)
| PreRef (_ : idx)
| PreApp (_ : op) (_ : list pre_expr).
(* note: need custom induction principle *)
Local Set Elimination Schemes.
Local Coercion PreARG : ARG >-> pre_expr.
Local Coercion PreFLG : FLAG >-> pre_expr.
Local Coercion PreRef : idx >-> pre_expr.
Example __testPreARG_boring : ARG -> list pre_expr := fun x : ARG => @cons pre_expr x nil.
(*
Example __testPreARG : ARG -> list pre_expr := fun x : ARG => [x].
*)

Fixpoint Symeval {descr:description} {s : OperationSize} {sa : AddressSize} (e : pre_expr) : M idx :=
  match e with
  | PreARG o => GetOperand o
  | PreFLG f => GetFlag f
  | PreRef i => ret i
  | PreApp op args =>
      idxs <- mapM Symeval args;
      App (op, idxs)
  end.

Definition rcrcnt s cnt : Z :=
  if N.eqb s 8 then Z.land cnt 31 mod 9 else
  if N.eqb s 16 then Z.land cnt 31 mod 17 else
  Z.land cnt (Z.of_N s-1).

Notation "f @ ( x , y , .. , z )" := (PreApp f (@cons pre_expr x (@cons pre_expr y .. (@cons pre_expr z nil) ..))) (at level 10) : x86symex_scope.
Definition SymexNormalInstruction {descr:description} (instr : NormalInstruction) : M unit :=
  let stack_addr_size : AddressSize := 64%N in
  let sa : AddressSize := 64%N in
  match Syntax.operation_size instr with Some s =>
  match Syntax.prefix instr with None =>
  let s : OperationSize := s in
  let resize_reg r := some_or (fun _ => reg_of_index_and_shift_and_bitcount_opt (reg_index r, 0%N (* offset *), s)) (fun _ => error.unimplemented_instruction instr) in
  match instr.(Syntax.op), instr.(args) with
  | (mov | movzx), [dst; src] => (* Note: unbundle when switching from N to Z *)
    v <- GetOperand src;
    SetOperand dst v
  | xchg, [a; b] => (* Note: unbundle when switching from N to Z *)
    va <- GetOperand a;
    vb <- GetOperand b;
    _ <- SetOperand b va;
    SetOperand a vb
  | cmovc, [dst; src]
  | cmovb, [dst; src]
    =>
    v <- Symeval (selectznz@(CF, dst, src));
    SetOperand dst v
  | cmovnz, [dst; src] =>
    v <- Symeval (selectznz@(ZF, src, dst));
    SetOperand dst v
  | seto, [dst] =>
    of <- GetFlag OF;
    SetOperand dst of
  | setc, [dst] =>
    cf <- GetFlag CF;
    SetOperand dst cf
  | Syntax.add, [dst; src] =>
    v <- Symeval (add s@(dst, src));
    c <- Symeval (addcarry s@(dst, src));
    o <- Symeval (addoverflow s@(dst, src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    _ <- SetFlag CF c;
    SetFlag OF o
  | Syntax.adc, [dst; src] =>
    v <- Symeval (add s@(dst, src, CF));
    c <- Symeval (addcarry s@(dst, src, CF));
    o <- Symeval (addoverflow s@(dst, src, CF));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    _ <- SetFlag CF c;
    SetFlag OF o
  | (adcx|adox) as op, [dst; src] =>
    let f := match op with adcx => CF | _ => OF end in
    v <- Symeval (add s@(dst, src, f));
    c <- Symeval (addcarry s@(dst, src, f));
    _ <- SetOperand dst v;
    SetFlag f c
  | Syntax.sub, [dst; src] =>
    v <- Symeval (add       s@(dst, PreApp (neg s) [PreARG src]));
    c <- Symeval (subborrow s@(dst, src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    SetFlag CF c
  | Syntax.sbb, [dst; src] =>
    v <- Symeval (add         s@(dst, PreApp (neg s) [PreARG src], PreApp (neg s) [PreFLG CF]));
    c <- Symeval (subborrow s@(dst, src, CF));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    SetFlag CF c
  | lea, [reg dst; mem src] =>
    a <- Address src;
    SetOperand dst a
  | imul, ([dst as src1; src2] | [dst; src1; src2]) =>
    v <- Symeval (mulZ@(src1,src2));
    _ <- SetOperand dst v;
    HavocFlags
  | Syntax.xor, [dst; src] =>
    v <- Symeval (xorZ@(dst,src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    zero <- Symeval (PreApp (const 0) nil);
    _ <- SetFlag CF zero;
    SetFlag OF zero
  | Syntax.and, [dst; src] =>
    v <- Symeval (andZ@(dst,src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    zero <- Symeval (PreApp (const 0) nil); _ <- SetFlag CF zero; SetFlag OF zero
  | Syntax.or, [dst; src] => (* side effects of "or" are identical to side effects of "and" and "xor", according to https://en.wikibooks.org/wiki/X86_Assembly/Logic *)
    v <- Symeval (orZ@(dst,src));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    zero <- Symeval (PreApp (const 0) nil); _ <- SetFlag CF zero; SetFlag OF zero
  | Syntax.bzhi, [dst; src; cnt] =>
    cnt <- GetOperand cnt;
    cnt <- RevealConst cnt;
    v <- Symeval (andZ@(src,PreApp (const (Z.ones (Z.land cnt (Z.ones 8)))) nil));
    _ <- SetOperand dst v;
    _ <- HavocFlags;
    zero <- App (const 0, nil); SetFlag OF zero
  | Syntax.rcr, [dst; cnt] =>
    x <- GetOperand dst;
    cf <- GetFlag CF;
    cnt <- GetOperand cnt; cnt <- RevealConst cnt; let cnt := rcrcnt s cnt in
    cntv <- App (const cnt, nil);
    y <- App (rcr s, [x; cf; cntv]);
    _ <- SetOperand dst y;
    _ <- HavocFlags;
    if (cnt =? 1)%Z
    then cf <- App ((slice 0 1), cons (x) nil); SetFlag CF cf
    else ret tt
  | mulx, [hi; lo; src2] =>
    let src1 : ARG := rdx in
    v  <- Symeval (mulZ@(src1,src2));
    vh <- Symeval (shrZ@(v,PreARG (Z.of_N s)));
    _ <- SetOperand lo v;
         SetOperand hi vh
  | (Syntax.mul | imul), [src2] =>
    let src1 : ARG := rax in
    v  <- Symeval (mulZ@(src1,src2));
    vh <- Symeval (shrZ@(v,PreARG (Z.of_N s)));
    lo <- resize_reg rax;
    hi <- (if (s =? 8)%N
           then ret ah
           else resize_reg rdx);
    _ <- SetOperand (lo:ARG) v;
    _ <- SetOperand (hi:ARG) vh;
    HavocFlags (* This is conservative and can be made more precise *)
  | Syntax.shl, [dst; cnt] =>
    let cnt := andZ@(cnt, (PreApp (const (Z.of_N s-1)%Z) nil)) in
    v <- Symeval (shl s@(dst, cnt));
    _ <- SetOperand dst v;
    HavocFlags
  | Syntax.shlx, [dst; src; cnt] =>
    cnt <- GetOperand cnt;
    cnt <- RevealConst cnt;
    let cnt' := andZ@(cnt, (PreApp (const (Z.of_N s-1)%Z) nil)) in
    v <- Symeval (shl s@(src, cnt'));
    SetOperand dst v
  | Syntax.shr, [dst; cnt] =>
    let cnt := andZ@(cnt, (PreApp (const (Z.of_N s-1)%Z) nil)) in
    v <- Symeval (shr s@(dst, cnt));
    _ <- SetOperand dst v;
    HavocFlags
  | Syntax.sar, [dst; cnt] =>
    x <- GetOperand dst;
    let cnt := andZ@(cnt, (PreApp (const (Z.of_N s-1)%Z) nil)) in
    c <- Symeval cnt; rc <- Reveal 1 c;
    y <- App (sar s, [x; c]);
    _ <- SetOperand dst y;
    _ <- HavocFlags;
    if expr_beq rc (ExprApp (const 1%Z, nil))
    then (
      cf <- App ((slice 0 1), cons (x) nil);
      _ <- SetFlag CF cf;
      zero <- App (const 0, nil); SetFlag OF zero)
    else ret tt
  | shrd, [lo as dst; hi; cnt] =>
    let cnt := andZ@(cnt, (PreApp (const (Z.of_N s-1)%Z) nil)) in
    let cnt' := addZ@(Z.of_N s, PreApp negZ [cnt]) in
    v <- Symeval (or s@(shr s@(lo, cnt), shl s@(hi, cnt')));
    _ <- SetOperand dst v;
    HavocFlags
  | inc, [dst] =>
    v <- Symeval (add s@(dst, PreARG 1%Z));
    o <- Symeval (addoverflow s@(dst, PreARG 1%Z));
    _ <- SetOperand dst v;
    _ <- PreserveFlag CF HavocFlags;
    SetFlag OF o
  | dec, [dst] =>
    v <- Symeval (add s@(dst, PreARG (-1)%Z));
    o <- Symeval (addoverflow s@(dst, PreARG (-1)%Z));
    _ <- SetOperand dst v;
    _ <- PreserveFlag CF HavocFlags;
    SetFlag OF o
  | test, [ea;eb] =>
    a <- GetOperand ea;
    b <- GetOperand eb;
    zero <- App (const 0, nil);
    _ <- HavocFlags;
    _ <- SetFlag CF zero;
    _ <- SetFlag OF zero;
    if Equality.ARG_beq ea eb
    then zf <- App (iszero, [a]); SetFlag ZF zf
    else ret tt
  | clc, [] => zero <- Merge (@ExprApp (const 0, nil)); SetFlag CF zero
  | push, [src]
    => v    <- GetOperand src;
       rsp' <- GetOperand (s:=stack_addr_size) rsp;
       rsp' <- Symeval (s:=stack_addr_size) (add stack_addr_size@(rsp', PreARG (-(Z.of_N s/8))%Z));
       _    <- SetOperand rsp rsp';
               SetOperand (mem_of_reg rsp) v
  | pop, [dst]
    => v    <- GetOperand (mem_of_reg rsp);
       rsp' <- GetOperand (s:=stack_addr_size) rsp;
       rsp' <- Symeval (s:=stack_addr_size) (add stack_addr_size@(rsp', PreARG ((Z.of_N s/8)%Z)));
       _    <- SetOperand rsp rsp';
               SetOperand dst v
  | _, _ => err (error.unimplemented_instruction instr)
 end
  | Some prefix => err (error.unimplemented_prefix instr) end
  | None => err (error.ambiguous_operation_size instr) end%N%x86symex.

Definition SymexRawLine {descr:description} (rawline : RawLine) : M unit :=
  match rawline with
  | EMPTY
  | LABEL _
    => ret tt
  | INSTR instr
    => SymexNormalInstruction instr
  | SECTION _
  | GLOBAL _
  | ALIGN _
  | DEFAULT_REL
      => err (error.unsupported_line rawline)
  end.

Definition SymexLine line :=
  let descr:description := Build_description (Parse.show_Line_with_line_number line) false in
  SymexRawLine line.(rawline).

Fixpoint SymexLines (lines : Lines) : M unit
  := match lines with
     | [] => ret tt
     | line :: lines
       => (st <- SymexLine line;
          SymexLines lines)
     end.
