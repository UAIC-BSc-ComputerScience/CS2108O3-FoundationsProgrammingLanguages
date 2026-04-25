Inductive Nat :=
| O : Nat
| S : Nat -> Nat.
Check Nat_ind.

Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | O => m (* O + m = m *)
  | S n' => S (plus n' m)
              (*S n + m = S (n + m)*)
  end.

Lemma O_plus_n_is_n:
  forall n, plus O n = n.
Proof.
  (* tactics *)
  intros n.
  simpl.
  reflexivity.
Qed.


Lemma n_plus_O_is_n:
  forall n, plus n O = n.
Proof.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma plus_comm:
  forall n m, plus n m = plus m n.
Proof.
  induction n.
  - intros m.
    simpl.
    rewrite n_plus_O_is_n.
    reflexivity.
  - induction m.
    + simpl.
      rewrite n_plus_O_is_n.
      reflexivity.
    + simpl.
      rewrite IHn.
      simpl.
      rewrite <- IHm.
      simpl.
      rewrite IHn.
      reflexivity.
Qed.
