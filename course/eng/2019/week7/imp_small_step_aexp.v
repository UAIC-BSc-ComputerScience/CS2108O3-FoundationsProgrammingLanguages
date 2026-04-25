Inductive Var :=
| x : Var
| y : Var
| n : Var
| i : Var
| sum : Var.

Fixpoint var_eq (v1 v2 : Var) :=
  match v1, v2 with
  | x, x => true
  | y, y => true
  | n, n => true
  | i, i => true
  | sum, sum => true
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
Check 5 +' 4 .
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

Reserved Notation "A -[ S ]-> N" (at level 60).

Inductive aeval_small_step :
  AExp -> State -> AExp -> Prop :=
| aconst : forall n st, n -[ st ]-> n
| alookup : forall v st, avar v -[ st ]-> (st v)
| aadd_1 : forall a1 a2 a1' st n,
    a1 -[ st ]-> a1' ->
    n = a1' +' a2 ->
    a1 +' a2 -[ st ]-> n
| aadd_2 : forall a1 a2 a2' st n,
    a2 -[ st ]-> a2' ->
    n = a1 +' a2' ->
    a1 +' a2 -[ st ]-> n
| aadd : forall i1 i2 st,
    (anum i1) +' (anum i2) -[ st ]-> i1 + i2
| atimes_1 : forall a1 a2 a1' st n,
    a1 -[ st ]-> a1' ->
    n = a1' *' a2 ->
    a1 *' a2 -[ st ]-> n
| atimes_2 : forall a1 a2 a2' st n,
    a2 -[ st ]-> a2' ->
    n = a1 *' a2' ->
    a1 *' a2 -[ st ]-> n
| atimes : forall i1 i2 st,
    (anum i1) *' (anum i2) -[ st ]-> i1 * i2
where "A -[ S ]-> N" := (aeval_small_step A S N).

Compute sigma1 x.

Example e1 :
  2 +' x -[ sigma1 ]-> 2 +' 10.
Proof.
  apply aadd_2 with (a2' := 10); auto.
  apply alookup.
Qed.


Reserved Notation "A -[ S ]*> N" (at level 60).
Inductive aeval_steps :
  AExp -> State -> AExp -> Prop :=
| refl : forall a st, a -[ st ]*> a
| tran : forall a1 a2 a3 st,
    a1 -[ st ]-> a2 ->
    a2 -[ st ]*> a3 ->
    a1 -[ st ]*> a3
where "A -[ S ]*> N" := (aeval_steps A S N).

Example e2 :
  2 +' x -[ sigma1 ]*> 12.
Proof.
  eapply tran.
  - apply e1.
  - eapply tran.
    + Check aadd.
      apply aadd.
    + simpl.
      apply refl.
Qed.
