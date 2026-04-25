Inductive Var := x | y | n | i | sum.

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
  | anum n' => n'
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


Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp.

Notation "A <=' B" := (blessthan A B) (at level 53).
Reserved Notation "B ={ State }=> B'" (at level 61).

Inductive beval : BExp -> State -> bool -> Prop :=
| etrue : forall state,
    btrue ={ state }=> true
| efalse : forall state,
    bfalse ={ state }=> false
| elessthan: forall a1 a2 i1 i2 state b,
    a1 =[state]=> i1 ->
    a2 =[state]=> i2 ->
    b = Nat.leb i1 i2 ->
    (a1 <=' a2) ={ state }=> b
| enottrue : forall b state,
    b ={ state }=> true ->
    (bnot b) ={ state }=> false
| enotfalse : forall b state,
    b ={ state }=> false ->
    (bnot b) ={ state }=> true
| eandtrue : forall b1 b2 state b,
    b1 ={state}=> true ->
    b2 ={state}=> b ->
    (band b1 b2) ={ state }=> b
| eandfalse : forall b1 b2 state,
    b1 ={state}=> false ->
    (band b1 b2) ={state}=> false
where "B ={ State }=> B'" := (beval B State B').

Example beval_lessthan:
  1 +' 3 <=' 5 ={ sigma0 }=> true.
Proof.
  eapply elessthan.
  - eapply aadd.
    + eapply aconst.
    + eapply aconst.
    + simpl. eauto.
  - eapply aconst.
  - simpl. reflexivity.
Qed.

Example beval_and_true:
  band (1 +' 3 <=' 5) (bnot btrue) ={sigma0}=> false.
Proof.
  eapply eandtrue.
  - apply beval_lessthan.
  - eapply enottrue.
    eapply etrue.
Qed.


Inductive Stmt :=
| assignment : Var -> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt.

Notation "X ::= N" := (assignment X N) (at level 60).
Notation "S ;; S'" := (sequence S S')
                        (at level 63, right associativity).

Reserved Notation "Stmt -{ State }-> State'" (at level 65).

Inductive eval : Stmt -> State -> State -> Prop :=
| eassign: forall var a state state' i,
    a =[state]=> i ->
    state' = update state var i ->
    (var ::= a) -{state}-> state'
| eseq : forall s1 s2 state1 state2 state,
    s1 -{state}-> state1 ->
    s2 -{state1}-> state2 ->
    (s1 ;; s2) -{state}-> state2
| ewhilefalse: forall state b s,
    b ={state}=> false ->
    (while b s) -{state}-> state
| ewhiletrue: forall state state' b s,
    b ={state}=> true ->
    (s ;; (while b s)) -{state}-> state' ->
    (while b s) -{state}-> state'
where "Stmt -{ State }-> State'" := (eval Stmt State State').

Example eval_assign:
  exists sigma,
    (x ::= 10) -{sigma0}-> sigma /\ sigma x = 10.
Proof.
  exists (update sigma0 x 10).
  split.
  - eapply eassign.
    eapply aconst.
    reflexivity.
  - unfold update.
    simpl.
    reflexivity.
Qed.

Example eval_assign_forall:
  forall sigma,
    (x ::= 10) -{sigma0}-> sigma -> sigma x = 10.
Proof.
  intros.
  inversion H.
  subst.
  inversion H2.
  subst.
  unfold update. simpl. reflexivity.
Qed.

Definition secventa := (x ::= 10);;(y ::= 1).
Example eval_seq:
  exists state,
    secventa -{sigma0}-> state /\ state x = 10 /\ state y = 1.
Proof.
  eexists.
  split.
  - unfold secventa.
    eapply eseq.
    + eapply eassign.
      eapply aconst.
      reflexivity.
    + eapply eassign.
      eapply aconst.
      reflexivity.
  - unfold update.
    simpl.
    split; trivial.
Qed.

Definition sumpgm_1 :=
  n ::= 1 ;;
  i ::= 1 ;;
  sum ::= 0 ;;
   while ( i <=' n)
   (sum ::= sum +' i ;; i ::= i +' 1).

Example eval_sumpgm_1:
  exists state,
    sumpgm_1 -{sigma0}-> state /\ state sum = 1.
Proof.
  eexists.
  unfold sumpgm_1.
  split.
  - eapply eseq.
    + eapply eassign.
      eapply aconst.
      trivial.
    + eapply eseq.
      * eapply eassign.
        eapply aconst.
        trivial.
      * eapply eseq.
        eapply eassign.
        eapply aconst.
        trivial.
        eapply ewhiletrue.
        ** eapply elessthan.
           eapply alookup.
           eapply alookup.
           simpl. reflexivity.
        ** eapply eseq.
           eapply eseq.
           eapply eassign.
           eapply aadd.
           eapply alookup.
           eapply alookup.
           unfold update. simpl. trivial.
           trivial.
           eapply eassign.
           eapply aadd.
           eapply alookup.
           eapply aconst.
           unfold update. simpl. trivial.
           trivial.
           eapply ewhilefalse.
           eapply elessthan.
           *** eapply alookup.
           *** eapply alookup.
           *** simpl. reflexivity.
  - unfold update. simpl. reflexivity.
Qed.

(*

Solution 1: use more automation tricks from Coq!

auto
eauto

Database: lemmas, theorems, axioms, definitions, etc.

 *)

Create HintDb mydb.
Hint Constructors aeval : mydb.
Hint Constructors beval : mydb.
Hint Constructors eval : mydb.
Hint Unfold update : mydb.

Example eval_sumpgm_1_automated:
  exists state,
    sumpgm_1 -{sigma0}-> state /\ state sum = 1.
Proof.
  eexists.
  unfold sumpgm_1.
  split.
  - eauto 20 with mydb.
  - auto.
Qed.



Definition sumpgm :=
  n ::= 4 ;;
  i ::= 1 ;;
  sum ::= 0 ;;
   while ( i <=' n)
   (sum ::= sum +' i ;; i ::= i +' 1).

Example eval_sumpgm_automated:
  exists state,
    sumpgm -{sigma0}-> state /\ state sum = 10.
Proof.
  eexists.
  unfold sumpgm.
  split.
  - eapply eseq.
    + eauto with mydb.
    + eapply eseq.
      ++ eauto with mydb.
      ++ eapply eseq.
         +++ eauto with mydb.
         +++ eapply ewhiletrue.
      * eauto with mydb.
      * eapply eseq.
        ** eauto 10 with mydb.
        ** eauto 40 with mydb.
  - auto.
Qed.

(*
Solution 2: prove an equivalence between eval (relation) and the eval function (with gas!)
 *)
