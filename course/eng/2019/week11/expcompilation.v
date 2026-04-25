Require Import String.
Require Import List.
Import ListNotations.

Definition Var := string.

Inductive Exp :=
| const : nat -> Exp
| id : Var -> Exp
| plus : Exp -> Exp -> Exp
| times : Exp -> Exp -> Exp.

Coercion const : nat >-> Exp.
Coercion id : Var >-> Exp.
Notation "A +' B" := (plus A B) (at level 50).
Notation "A *' B" := (times A B) (at level 48).

Open Scope string_scope.

Eval compute in (const 5).
Eval compute in (id "a").
Eval compute in (id "a") +' 4.
Eval compute in (id "a") *' 4.

Fixpoint interpret (e : Exp)
         (env : Var -> nat) : nat :=
  match e with
  | const c => c
  | id x => (env x)
  | plus e1 e2 => (interpret e1 env) +
                  (interpret e2 env)
  | times e1 e2 => (interpret e1 env) *
                   (interpret e2 env)
  end.

Definition Env :=
  fun x => if string_dec x "a" then 10 else 0.

Eval compute in (Env "a").
Eval compute in (Env "b").


Eval compute in (interpret (const 5) Env).
Eval compute in (interpret (id "a") Env).
Eval compute in (interpret ((id "a") +' 4) Env).
Eval compute in (interpret ((id "a") *' 4) Env).


(* Define a stack machine *)
Inductive Instruction :=
| push_const : nat -> Instruction
| push_var : Var -> Instruction
| add : Instruction
| mul : Instruction.


Fixpoint run_instruction (i : Instruction)
         (env : Var -> nat) (stack : list nat) :=
  match i with
  | push_const c => (c :: stack)
  | push_var x => ((env x) :: stack)
  | add => match stack with
           | n1 :: n2 :: stack' => (n1 + n2) :: stack'
           | _ => stack
           end
  | mul => match stack with
           | n1 :: n2 :: stack' => (n1 * n2) :: stack'
           | _ => stack
           end
  end.

Eval compute in (push_const 10).
Eval compute in (run_instruction
                   (push_const 10)
                   Env
                   nil).
Eval compute in (run_instruction
                   (push_var "x")
                   Env
                   nil).
Eval compute in (run_instruction
                   (push_var "a")
                   Env
                   nil).
Eval compute in (run_instruction
                   add
                   Env
                   (5 :: 6 :: 1 :: 4 :: nil)
                ).
Eval compute in (run_instruction
                   mul
                   Env
                   (5 :: 6 :: 1 :: 4 :: nil)
                ).
Eval compute in (run_instruction
                   add
                   Env
                   (4 :: nil)
                ).
Eval compute in (run_instruction
                   add
                   Env
                   nil
                ).


Fixpoint run_instructions (is' : list Instruction)
         (env : Var -> nat) (stack : list nat) :=
  match is' with
  | nil => stack
  | i :: is'' => run_instructions
                   is''
                   env
                   (run_instruction i env stack)
  end.

Definition pgm1 :=
  [(push_const 5); (push_var "a") ; add].

Definition pgm2 :=
  [ (push_const 10) ; (push_var "a") ; (push_var "b") ; add ; mul].

Eval compute in
    run_instructions pgm1 Env nil.

Eval compute in
    run_instructions pgm2 Env nil.


(* Compilation *)
Fixpoint compile (e : Exp) : list Instruction :=
  match e with
  | const c => [push_const c]
  | id x => [push_var x]
  | plus e1 e2 => (compile e1) ++ (compile e2)
                               ++ (add :: nil)
  | times e1 e2 => (compile e1) ++ (compile e2)
                                ++ (mul :: nil)
  end.

Eval compute in compile ((id "a") +' 4 *' (id "a")).

Eval compute in interpret
                  ((id "a") +' 4 *' (id "a"))
                  Env.

Eval compute in
    run_instructions
      (compile ( ((id "a") +' 4 *' (id "a"))))
      Env
      nil.


Lemma soundness_helper :
  forall e env stack is',
    run_instructions (compile e ++ is')
                     env stack =
    run_instructions is' env
                     ((interpret e env) :: stack).
Proof.
  induction e; intros; simpl; trivial.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    rewrite PeanoNat.Nat.add_comm.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    rewrite PeanoNat.Nat.mul_comm.
    reflexivity.
Qed.

Theorem soundness :
  forall e env,
    run_instructions (compile e) env nil =
    [interpret e env].
Proof.
  intros.
  rewrite <- app_nil_r with (l := compile e).
  rewrite soundness_helper. simpl.
  trivial.
Qed.
