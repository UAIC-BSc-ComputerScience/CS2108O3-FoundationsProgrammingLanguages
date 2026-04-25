Module Naturals.

  Inductive Nat : Set :=
  | O : Nat
  | S : Nat -> Nat .

  Eval compute in (S O) .

  (* addition *)
  Fixpoint add (n m : Nat) : Nat :=
    match n with
    | O => m  (* 0 + m = m *)
    | S n' => S (add n' m) (* S n' + m = S (n' + m) *)
    end.

  (* 1 + 2 = 3 *)
  Eval compute in (add (S O) (S (S O))) .

  Lemma n_plus_zero:
    (* forall n, n + O = n *)
    forall n, add n O = n.
  Proof.
    (* tactics *)

    (* P(0)   /\  P(k) -> P(k+1) *)
    induction n.
    - simpl. reflexivity.
    - simpl.
      rewrite IHn.
      reflexivity.
  Qed.

  Lemma zero_plus_n:
    forall n, add O n = n.
  Proof.
    intros n.
    simpl.
    reflexivity.
  Qed.

  Lemma plus_comm:
    forall a b, add a b = add b a.
  Proof.
    induction a.
    - intros b.
      rewrite n_plus_zero.
      rewrite zero_plus_n.
      reflexivity.
    - induction b.
      + rewrite n_plus_zero, zero_plus_n.
        reflexivity.
      + simpl.
        rewrite <- IHb.
        simpl.
        rewrite IHa.
        simpl.
        rewrite IHa.
        reflexivity.
  Qed.
  
End Naturals.