Inductive Var := n | i | sum.
Definition var_eq ( v1 v2 : Var) : bool :=
  match v1, v2 with
  | n, n => true
  | i, i => true
  | sum, sum => true
  | _,_ => false
  end.

Compute (var_eq n n).
Compute (var_eq n i).

(* Environment *)
Definition Env := Var -> nat.
Definition env1 : Env :=
  fun x =>
    if (var_eq x n)
    then 10
    else 0.
Check env1.

Compute (env1 sum).

Definition update (env : Env)
           (x : Var) (v : nat) : Env :=
  fun y =>
    if (var_eq y x)
    then v
    else (env y).
Check update.
Definition env2 := (update env1 n 1045).
Compute (env2 n).

Inductive AExp :=
| avar : Var -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp.

Notation "A +' B" := (aplus A B) (at level 48).
Notation "A *' B" := (amul A B) (at level 46).
Coercion anum : nat >-> AExp.
Coercion avar : Var >-> AExp.
Check (2 +' 3 *' 5).
Check (2 +' 3 *' n).


Fixpoint aeval (a : AExp) (env : Env) : nat :=
  match a with
  | avar x => env x
  | anum v => v
  | aplus a1 a2 => (aeval a1 env) + (aeval a2 env)
  | amul a1 a2 => (aeval a1 env) * (aeval a2 env)
  end.

Compute aeval (2 *' 3 *' 5) env1.
Compute aeval (2 +' 3 *' n) env1.


Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp.

Fixpoint beval (b : BExp) (env : Env) : bool :=
  match b with
  | btrue => true
  | bfalse => false
  | blessthan a1 a2 => Nat.leb (aeval a1 env)
                               (aeval a2 env)
  | bnot b' => negb (beval b' env)
  end.

Notation "A <<= B" := (blessthan A B) (at level 58).

Compute beval (bnot (n <<= (2 +' 3 *' n))) env1.

(* n ::= 10 *)
Inductive Stmt :=
| assignment : Var -> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt.

Notation "X ::= N" := (assignment X N) (at level 60).
Notation "S ;; S'" := (sequence S S')
                        (at level 63, right associativity).

Check (n ::= n +' 10).
Check (n ::= 0 ;; i ::= 7 ;; sum ::= 0).

Fixpoint eval (s : Stmt) (env : Env) (gas : nat) : Env :=
  match gas with
  | 0 => env
  | S gas' => match s with
              | assignment x a => update env x (aeval a env)
              | sequence s1 s2 => eval s2 (eval s1 env gas') gas'
              | while b s => if (beval b env)
                             then (eval
                                     (sequence s (while b s))
                                     env gas')
                             else env
              end
  end.
  
  Definition pgm  := (n ::= 7).
  Definition env_after_assign := eval pgm env1 10.
Compute env_after_assign n.

Definition pgm2  := n ::= 243 ;; i ::= 7 ;; sum ::= 10.

Compute (eval pgm2 env1 10) n.
Compute (eval pgm2 env1 10) i.
Compute (eval pgm2 env1 10) sum.

Definition sumpgm :=
  n ::= 10 ;;
  i ::= 1 ;;
  sum ::= 0 ;;
   while ( i <<= n)
   (sum ::= sum +' i ;; i ::= i +' 1).
Check sumpgm.

Compute (eval sumpgm env1 1000) sum.












