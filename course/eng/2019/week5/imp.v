Inductive Var := x | y.

Fixpoint var_eq (v1 v2 : Var) :=
  match v1, v2 with
  | x, x => true
  | y, y => true
  | _, _ => false
  end.

Inductive AExp :=
| anum : nat -> AExp
| avar : Var -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp.

Notation "A +' B" := (aplus A B) (at level 50).
Notation "A *' B" := (amul A B) (at level 46).

Coercion anum : nat >-> AExp.
Coercion avar : Var >-> AExp.

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

Inductive aeval : AExp -> State -> nat -> Prop :=
| aconst : forall n st, anum n =[ st ]=> n
| alookup : forall v st, avar v =[ st ]=> (st v)
| aadd : forall a1 a2 i1 i2 st n,
    a1 =[ st ]=> i1 ->
    a2 =[ st ]=> i2 ->
    n = i1 + i2 ->
    a1 +' a2 =[ st ]=> n
| atimes : forall a1 a2 i1 i2 st n,
    a1 =[ st ]=> i1 ->
    a2 =[ st ]=> i2 ->
    n = i1 * i2 ->
    a1 *' a2 =[ st ]=> n
where "A =[ S ]=> N" := (aeval A S N).


Example e1 :
  2 +' x =[ sigma1 ]=> 2 + 10.
Proof.
  apply aadd with
      (i1 := 2)(i2 := 10); auto.
  - apply aconst.
  - apply alookup.
Qed.


Example e2 :
  2 +' x =[ sigma1 ]=> 12.
Proof.
  apply aadd with
      (i1 := 2)(i2 := 10); auto.
  - apply aconst.
  - apply alookup.
Qed.

Example e2' :
  2 +' x =[ sigma1 ]=> 12.
Proof.
  eapply aadd.
  - apply aconst.
  - apply alookup.
  - auto.
Qed.


Lemma aeval_is_deterministic:
  forall aexp st n n',
    aexp =[ st ]=> n ->
    aexp =[ st ]=> n' ->
    n = n'.
Proof.
  induction aexp; intros;
    inversion H; inversion H0;
      subst; auto.
  - assert (IH1: i1 = i0).
    eapply IHaexp1; eauto.
    assert (IH2 : i2 = i3).
    eapply IHaexp2; eauto.
    subst.
    reflexivity.
  - assert (IH1: i1 = i0).
    eapply IHaexp1; eauto.
    assert (IH2 : i2 = i3).
    eapply IHaexp2; eauto.
    subst.
    reflexivity.
Qed.


Fixpoint aeval_fun (a : AExp) (sigma : State):=
  match a with
  | anum n => n
  | avar v => sigma v
  | a1 +' a2 => (aeval_fun a1 sigma) +
                (aeval_fun a2 sigma)
  | a1 *' a2 => (aeval_fun a1 sigma) *
                (aeval_fun a2 sigma)
  end.

Compute (aeval_fun (2 +' 3)).

Lemma equiv :
  forall a st,
    a =[ st ]=> (aeval_fun a st).
Proof.
  induction a; intros; simpl.
  - apply aconst.
  - apply alookup.
  - eapply aadd; eauto.
  - eapply atimes; eauto.
Qed.
