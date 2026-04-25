Inductive Var := x | y | n | i | sum.

Fixpoint var_eq (v1 v2 : Var) :=
  match v1, v2 with
  | x, x => true
  | y, y => true
  | n, n => true
  | i, i => true
  | sum, sum => true
  | _, _ => false
  end.

Inductive Exp :=
| anum : nat -> Exp
| avar : Var -> Exp
| aplus : Exp -> Exp -> Exp
| amul : Exp -> Exp -> Exp
| btrue : Exp
| bfalse : Exp
| blessthan : Exp -> Exp -> Exp
| bnot : Exp -> Exp
| band : Exp -> Exp -> Exp.

Coercion anum : nat >-> Exp.
Coercion avar : Var >-> Exp.
Notation "A +' B" := (aplus A B) (at level 50).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A <=' B" := (blessthan A B) (at level 53).


Eval compute in (2 +' 2).
Eval compute in (2 +' btrue).
Eval compute in (band 2 2).


Definition State := Var -> nat.
(* lookup:  *)
Definition sigma0 : State := fun n => 0.
Check sigma0.
Compute (sigma0 x).
Compute (sigma0 y).


(* update *)
Definition update (sigma : State)
           (v : Var) (val : nat) : State :=
  fun v' => if (var_eq v v')
            then val
            else (sigma v').
Definition sigma1 := (update sigma0 x 10).
Compute (sigma1 x).

Reserved Notation "A =[ S ]=> N" (at level 60).

Inductive exp_eval_small_step : Exp -> State -> Exp -> Prop :=
| econst : forall n st, anum n =[ st ]=> n
| elookup : forall v st, avar v =[ st ]=> (st v)
| eadd_1 : forall a1 a2 a1' st a,
    a1 =[ st ]=> a1' ->
    a = a1' +' a2 ->
    a1 +' a2 =[ st ]=> a
| eadd_2 : forall a1 a2 a2' st a,
    a2 =[ st ]=> a2' ->
    a = a1 +' a2' ->
    a1 +' a2 =[ st ]=> a
| eadd : forall i1 i2 st n,
    n = anum (i1 + i2) ->
    anum i1 +' anum i2 =[ st ]=> n
| etimes_1 : forall a1 a2 a1' st a,
    a1 =[ st ]=> a1' ->
    a = a1' *' a2 ->
    a1 *' a2 =[ st ]=> a
| etimes_2 : forall a1 a2 a2' st a,
    a2 =[ st ]=> a2' ->
    a = a1 *' a2' ->
    a1 *' a2 =[ st ]=> a
| etimes : forall i1 i2 st n,
    n = anum (i1 + i2) ->
    anum i1 *' anum i2 =[ st ]=> n
| etrue : forall st, btrue =[ st ]=> btrue
| efalse : forall st, bfalse =[ st ]=> bfalse
| elessthan_1: forall a1 a2 a1' state,
    a1 =[ state ]=> a1' ->
    (a1 <=' a2) =[ state ]=> a1' <=' a2
| elessthan_2: forall i1 a2 a2' state,
    a2 =[state]=> a2' ->
    (anum i1) <=' a2 =[ state ]=> (anum i1) <=' a2'
| elessthan: forall i1 i2 state b,
    b = (if Nat.leb i1 i2 then btrue else bfalse) ->
    (anum i1) <=' (anum i2) =[ state ]=> b
| enot : forall b b' state,
    b =[ state ]=> b' ->
    (bnot b) =[ state ]=> (bnot b')
| enottrue : forall state,
    (bnot btrue) =[ state ]=> bfalse
| enotfalse : forall state,
    (bnot bfalse) =[ state ]=> btrue
| eand_1 : forall b b1 b1' b2 state,
    b1 =[state]=> b1' ->
    b = (band b1' b2) ->
    (band b1 b2) =[ state ]=> b
| eandtrue : forall b2 state,
    (band btrue b2) =[state]=> b2
| eandfalse : forall b2 state,
    (band bfalse b2) =[state]=> bfalse
where "A =[ S ]=> N" := (exp_eval_small_step A S N).


Example e1 :
  2 +' x =[ sigma1 ]=> 2 +' 10.
Proof.
  eapply eadd_2.
  eapply elookup.
  unfold sigma1, update.
  simpl.
  reflexivity.
Qed.

Reserved Notation "A =[ S ]>* A'" (at level 60).
Inductive aeval_clos : Exp -> State -> Exp -> Prop :=
| e_refl : forall a st, a =[ st ]>* a
| e_trans : forall a1 a2 a3 st,  (a1 =[st]=> a2) -> a2 =[ st ]>* a3  -> a1 =[ st ]>* a3
where "A =[ S ]>* A'" := (aeval_clos A S A').

Example e2 :
  2 +' x =[ sigma1 ]>* anum 12.
Proof.
  eapply e_trans.
  - eapply eadd_2.
    eapply elookup. eauto.
  - eapply e_trans.
    + eapply eadd. eauto.
    + simpl. eapply e_refl.
Qed.


(* Typing *)
Inductive Typ : Type :=
| Bool : Typ
| Nat : Typ.
Print Exp.
Inductive type_of : Exp -> Typ -> Prop :=
| typ_num : forall n, type_of (anum n) Nat
| typ_var : forall x, type_of (avar x) Nat
| typ_plus : forall a1 a2,
    type_of a1 Nat ->
    type_of a2 Nat ->
    type_of (a1 +' a2) Nat
| typ_mul : forall a1 a2,
    type_of a1 Nat ->
    type_of a2 Nat ->
    type_of (a1 *' a2) Nat
| typ_true : type_of btrue Bool
| typ_false : type_of bfalse Bool
| typ_lessthan : forall a1 a2,
    type_of a1 Nat ->
    type_of a2 Nat ->
    type_of (a1 <=' a2) Bool
| typ_not : forall b,
    type_of b Bool ->
    type_of (bnot b) Bool
| typ_and : forall b1 b2,
    type_of b1 Bool ->
    type_of b2 Bool ->
    type_of (band b1 b2) Bool.

Example well_typed:
  type_of (2 +' x) Nat.
Proof.
  apply typ_plus.
  - apply typ_num.
  - apply typ_var.
Qed.

Example ill_typed:
  type_of (2 +' btrue) Nat.
Proof.
  apply typ_plus.
  - apply typ_num.
  - (* can't prove that *)
Admitted.

Example well_typed_bool:
  type_of (2 <=' x) Bool.
Proof.
  apply typ_lessthan.
  - apply typ_num.
  - apply typ_var.
Qed.

Example lessthan_has_type_Bool_args_have_type_Nat:
  forall a1 a2,
    type_of (a1 <=' a2) Bool ->
    type_of a1 Nat /\ type_of a2 Nat.
Proof.
  split; inversion H; assumption.
Qed.

(* Canonical forms *)
(* Values *)
Inductive nat_value : Exp -> Prop :=
| nat_val : forall n, nat_value (anum n).

Inductive b_value : Exp -> Prop :=
| b_true : b_value btrue
| b_false : b_value bfalse.

Definition value (e : Exp) := nat_value e \/ b_value e.

Lemma bool_canonical :
  forall e, type_of e Bool -> value e -> b_value e.
Proof.
  intros.
  unfold value in H0.
  destruct H0 as [H0 | H0].
  - inversion H.
    + apply b_true.
    + apply b_false.
    + rewrite <- H3 in H0. inversion H0.
    + rewrite <- H2 in H0. inversion H0.
    + rewrite <- H3 in H0. inversion H0.
  - assumption.
Qed.

Lemma nat_canonical :
  forall e, type_of e Nat -> value e -> nat_value e.
Proof.
  intros.
  inversion H0; trivial.
  inversion H; subst; inversion H1.
Qed.


Hint Constructors exp_eval_small_step.
Hint Constructors type_of.
Hint Constructors nat_value.
Hint Constructors b_value.

(* Progress *)
Theorem progress :
  forall t T state,
    type_of t T ->
    value t \/ exists t', t =[ state ]=> t'.
Proof.
  intros.
  induction H.
  - left. unfold value. left. eapply nat_val.
  - right. eexists. eapply elookup.
  - inversion IHtype_of1.
    + inversion IHtype_of2.
      * inversion H1.
        ** inversion H3. subst.
           inversion H2. inversion H4. subst.
           *** right. eexists. eapply eadd. eauto.
           *** inversion H4; subst; inversion H0.
        ** inversion H3; subst; inversion H.
      * right. destruct H2 as [t' H2]. eexists. eapply eadd_2; eauto.
    + right. destruct H1 as [t' H1]. eexists. eapply eadd_1; eauto.
  - inversion IHtype_of1.
    + inversion IHtype_of2.
      * inversion H1.
        ** inversion H3. subst.
           inversion H2. inversion H4. subst.
           *** right. eexists. eapply etimes. eauto.
           *** inversion H4; subst; inversion H0.
        ** inversion H3; subst; inversion H.
      * right. destruct H2 as [t' H2]. eexists. eapply etimes_2; eauto.
    + right. destruct H1 as [t' H1]. eexists. eapply etimes_1; eauto.
  - left. unfold value. eauto.
  - left. unfold value. eauto.
  - inversion IHtype_of1.
    + inversion IHtype_of2.
      * inversion H1.
        ** inversion H3. subst.
           inversion H2. inversion H4. subst.
           *** right. eexists. eapply elessthan. eauto.
           *** inversion H4; subst; inversion H0.
        ** inversion H3; subst; inversion H.
      * right.
        ** inversion H1. inversion H3. subst.
           destruct H2 as [t' H2]. eexists. eapply elessthan_2; eauto.
           inversion H3; subst; inversion H.
    + right. destruct H1 as [t' H1]. eexists. eapply elessthan_1; eauto.
  - inversion IHtype_of.
    + right. eexists.
      inversion H0.
      * inversion H1; subst. inversion H.
      * inversion H1; subst; eapply enot. eapply etrue. eapply efalse.
    + destruct H0 as [t' H0].
      right. eexists. eapply enot. exact H0.
  - inversion IHtype_of1.
    + inversion IHtype_of2.
      * inversion H1.
        ** inversion H3; subst. inversion H.
        ** inversion H3; subst.
           *** right. eexists. eapply eand_1. eapply etrue. eauto.
           *** right. eexists. eapply eand_1. eapply efalse. eauto.
      * inversion H1.
        ** inversion H3; subst. inversion H.
        ** right. destruct H2 as [t' H2]. eexists.
           eapply eand_1; eauto. inversion H3; subst.
           eapply etrue.
           eapply efalse.
    + right. destruct H1 as [t' H1]. eexists. eapply eand_1.
      eapply H1. trivial.
Qed.


(* Type preservation *)
Theorem preservation :
  forall t T t' state,
    type_of t T ->
    t =[ state ]=> t' ->
    type_of t' T.
Proof.
  intros.
  revert t' H0.
  induction H; intros t' H''; inversion H''; subst; eauto.
    case_eq (Nat.leb i1 i2); intros H'; rewrite H' in *; eauto.
Qed.

(* Type soundness *)
Corollary soundness :
  forall t t' state T,
    type_of t T ->
    t =[ state ]>* t' ->
    value t' \/ exists t'', t' =[ state ]=> t''.
Proof.
  intros.
  induction H0.
  - eapply progress. eauto.
  - apply IHaeval_clos. eapply preservation; eauto.
Qed.

Print soundness.
