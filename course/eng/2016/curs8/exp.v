Require Import String.
Require Import List.

Module Exp.

  (* syntax *)
  (* Exp ::= Nat | Id | Exp + Exp | Exp * Exp *)
  Inductive Exp : Set :=
  | Const : nat -> Exp
  | Var : string -> Exp
  | Plus : Exp -> Exp -> Exp
  | Times : Exp -> Exp -> Exp .
  
  Eval compute in (Const 2) .
  Eval compute in (Var "a") .
  Eval compute in (Plus (Const 2) (Var "a")) .

  (* semantics *)
  Fixpoint interpret
           (e : Exp) (map : string -> nat)
    : nat :=
    match e with
    | Const k => k
    | Var x => (map x)
    | Plus e1 e2 =>
      (interpret e1 map) + (interpret e2 map)
    | Times e1 e2 =>
      (interpret e1 map) * (interpret e2 map)
    end.

  Definition env (x : string) : nat :=
    if (string_dec x "a")
    then 10
    else 0 .
           
           
  Check env.

  (* intepret(2+a) *)
  Eval compute in
      (interpret
         (Times (Const 2) (Var "a"))
         env
      ).
                             


  (* stack machine *)

  (* syntax asm *)
  Inductive instruction : Set :=
  | push_const : nat -> instruction
  | push_var : string -> instruction
  | add : instruction
  | mul : instruction .

  Eval compute in (push_const 3).


  (* semantics using a stack! *)
  Fixpoint run_instruction
           (i : instruction)
           (map : string -> nat)
           (stack : list nat)
    : list nat :=
    match i with
    | push_const k => k :: stack
    | push_var x => (map x) :: stack
    | add => match stack with
             | arg1 :: arg2 :: rest =>
               (arg1 + arg2) :: rest
             | _ => stack
             end
    | mul => match stack with
             | arg1 :: arg2 :: rest =>
               (arg1 * arg2) :: rest
             | _ => stack
             end
    end.

  Eval compute in
      (run_instruction
         add
         env
         (192 :: 3 :: nil)) .

  Fixpoint run (is : list instruction)
           (map : string -> nat)
           (stack : list nat)
    : list nat :=
    match is with
    | nil => stack
    | i :: is' =>
      run is' map
          (run_instruction i map stack)
    end.


  Eval compute in
      (run
         (push_var "a" :: push_const 3 ::
                   add :: nil)
         env
         (24 :: nil) ).




  (* compilation *)
  Fixpoint compile (e : Exp)
    : list instruction :=
    match e with
    | Const k => (push_const k :: nil)
    | Var x => (push_var x :: nil)
    | Plus e1 e2 =>
      (compile e1) ++ (compile e2) ++
                   (add :: nil)
    | Times e1 e2 =>
      (compile e1) ++ (compile e2) ++
                   (mul :: nil)
    end.


  
  Eval compute in
      run
        (compile (Plus (Const 2) (Var "a")))
        env
        nil
  .
                   


  (* Prove that our compiler is correct *)
  Lemma compiler_correct' :
    forall e m is stack,
      run (compile e ++ is) m stack =
      run is m (interpret e m :: stack).
  Proof.
    induction e.
    - intros. simpl. reflexivity.
    - intros. simpl. reflexivity.
    - intros.
      simpl.
      Check app_assoc_reverse.
      rewrite app_assoc_reverse.
      rewrite IHe1.
      rewrite app_assoc_reverse.
      rewrite IHe2.
      simpl.
      rewrite PeanoNat.Nat.add_comm.
      trivial.
    - intros.
      simpl.
      Check app_assoc_reverse.
      rewrite app_assoc_reverse.
      rewrite IHe1.
      rewrite app_assoc_reverse.
      rewrite IHe2.
      simpl.
      rewrite PeanoNat.Nat.mul_comm.
      trivial.
  Qed.
      
      
  Theorem compiler_correct:
    forall e m,
      run (compile e) m nil =
      (interpret e m) :: nil .
  Proof.
    intros.
    rewrite <- app_nil_r with (l := compile e).
    rewrite compiler_correct'.
    simpl.
    reflexivity.
  Qed.
  
  
End Exp.

