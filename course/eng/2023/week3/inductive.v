Inductive Nat :=
| O : Nat
| S : Nat -> Nat.

Check Nat_ind.

Check (S (S O)).
Check S.

(*
O   + m = m
(S n) + m = S (n + m)

*)


Fixpoint plus (k m : Nat) : Nat :=
  match k with
  | O   => m
  | S n => S (plus n m)
  end.

Compute plus O (S (S O)).
Compute plus (S (S O)) (S (S O)).


Lemma plus_O_m_is_m :
  forall m, plus O m = m.
Proof.
  (* tactics *)
  intro m.
  simpl.
  reflexivity.
Qed.

Theorem plus_eq :
  forall m n, m = n -> plus O m = plus O n.
Proof.
  intros m n H.
  rewrite <- H.
  trivial.
Qed.

Theorem plus_neq:
  forall m n, m <> n -> plus O m <> plus O n.
Proof.
  intros m n H.
  Locate "<>".
  unfold not.
  intros H'.
  simpl in H'.

  (* variant 1 *)
  (* rewrite H' in H. *)
  (* unfold not in H. *)
  (* apply H. *)
  (* reflexivity. *)

  (* variant 2 *)
  (* contradict H'. *)
  (* assumption. *)
    
  (* variant 3 *)
  contradiction.
Qed.

Theorem plus_c_a:
  forall k, plus k (S O) <> O.
Proof.
  intro k.
  unfold not.
  intro H.
  destruct k as [| k']; simpl in H; discriminate H.
Qed.


Lemma plus_m_O_is_m:
  forall m,
    plus m O = m.
Proof.
  induction m.
  - simpl. reflexivity.
  - simpl. rewrite IHm. reflexivity.
Qed.

Lemma plus_n_Sm_is_Snm:
  forall n m,
    plus n (S m) = S (plus n m).
Proof.
  induction n.
  - intro m. simpl. reflexivity.
  - intro m. simpl. rewrite IHn. reflexivity.
Qed.

Lemma plus_comm:
  forall m n,
    plus m n = plus n m.
Proof.
  induction m; intro n; simpl.
  - rewrite plus_m_O_is_m.
    reflexivity.
  - rewrite plus_n_Sm_is_Snm.
    rewrite IHm.
    reflexivity.
Qed.


Lemma plus_assoc:
  forall m n k,
    plus (plus m n) k = plus m (plus n k).
Proof.
  





  
