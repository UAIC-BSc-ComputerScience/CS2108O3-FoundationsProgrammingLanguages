Inductive BinTree :=
| leaf : BinTree
| node : nat -> BinTree -> BinTree  -> BinTree.


Check BinTree_ind.

(*         . *)
(* ------------------ *)
(*   leaf in BinTree *)

(* n in  nat  l in BinTree    r in BinTree  *)
(* ----------------------------------------- *)
(*            (node n l r)  in BinTree *)

(* P(leaf) *)
(* (P(l) /\ P(r)) --> P(node n l r) *)

Require Import List.
Import ListNotations.

Fixpoint preorder (b : BinTree) : list nat :=
  match b with
  | leaf => []
  | node n ltree rtree =>
    n :: (preorder ltree) ++ (preorder rtree)
  end.


Definition one := (node 1 leaf leaf).
Definition two := (node 2 leaf leaf).
Definition three := (node 3 one two).

Compute (preorder one).
Compute (preorder leaf).
Compute (preorder three).

Fixpoint search (b : BinTree) (x : nat) :=
  match b with
  | leaf => false
  | node n ltree rtree =>
    if (Nat.eqb n x)
    then true
    else orb (search ltree x) (search rtree x)
  end.

Compute (search three 0).
Compute (search three 1).
Compute (search three 2).
Compute (search three 3).
Compute (search three 5).

Lemma search_correct:
  forall b x,
    In x (preorder b) -> search b x = true.
Proof.
  induction b.
  - intros.
    simpl.
    simpl in H.
    contradiction.
  - intros.
    simpl in H.
    destruct H as [H | H].
    + rewrite H.
      simpl.
      SearchPattern (Nat.eqb _ _ = _).
      rewrite PeanoNat.Nat.eqb_refl.
      trivial.
    + simpl in H.
      SearchPattern (In _ (_ ++ _) <-> _).
      rewrite in_app_iff in H.
      destruct H as [H | H].
      * simpl.
        case_eq (Nat.eqb n x).
        ** intros H'. trivial.
        ** intros H'.
           apply IHb1 in H.
           rewrite H.
           simpl.
           trivial.
      * simpl.
        case_eq (Nat.eqb n x).
        ** intros H'. reflexivity.
        ** intros H'.
           apply IHb2 in H.
           rewrite H.
           simpl.
           SearchPattern (orb _ _ = _).
           rewrite Bool.orb_true_r.
           trivial.
Qed.
