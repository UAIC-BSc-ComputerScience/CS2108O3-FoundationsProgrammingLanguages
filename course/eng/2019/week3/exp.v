Inductive Exp :=
| number : nat -> Exp
| plus : Exp -> Exp -> Exp.

Compute (number 0).
Compute (plus (number 0) (number 7)).

Coercion number : nat >-> Exp.

Compute (plus 0 7).

Notation "A +' B" := (plus A B) (at level 49, right associativity).
Compute (0 +' 7 +' 6).
