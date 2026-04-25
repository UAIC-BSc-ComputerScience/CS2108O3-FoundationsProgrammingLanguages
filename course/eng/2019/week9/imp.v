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

Inductive aeval_small_step : AExp -> State -> AExp -> Prop :=
| aconst : forall n st, anum n =[ st ]=> n
| alookup : forall v st, avar v =[ st ]=> (st v)
| aadd_1 : forall a1 a2 a1' st,
    a1 =[ st ]=> a1' ->
    a1 +' a2 =[ st ]=> a1' +' a2
| aadd_2 : forall a1 a2 a2' st,
    a2 =[ st ]=> a2' ->
    a1 +' a2 =[ st ]=> a1 +' a2'
| aadd : forall i1 i2 st n,
    n = anum (i1 + i2) ->
    anum i1 +' anum i2 =[ st ]=> n
| atimes_1 : forall a1 a2 a1' st,
    a1 =[ st ]=> a1' ->
    a1 *' a2 =[ st ]=> a1' *' a2
| atimes_2 : forall a1 a2 a2' st,
    a2 =[ st ]=> a2' ->
    a1 *' a2 =[ st ]=> a1 *' a2'
| atimes : forall i1 i2 st n,
    n = anum (i1 + i2) ->
    anum i1 *' anum i2 =[ st ]=> n
where "A =[ S ]=> N" := (aeval_small_step A S N).


Example e1 :
  2 +' x =[ sigma1 ]=> 2 +' 10.
Proof.
  eapply aadd_2.
  eapply alookup.
Qed.

Reserved Notation "A =[ S ]>* A'" (at level 60).
Inductive aeval_clos : AExp -> State -> AExp -> Prop :=
| a_refl : forall a st, a =[ st ]>* a
| a_trans : forall a1 a2 a3 st,  (a1 =[st]=> a2) -> a2 =[ st ]>* a3  -> a1 =[ st ]>* a3
where "A =[ S ]>* A'" := (aeval_clos A S A').

Example e2 :
  2 +' x =[ sigma1 ]>* anum 12.
Proof.
  apply a_trans with (a2 := (2 +' 10)).
  - apply aadd_2.
    apply alookup.
  - eapply a_trans.
    + eapply aadd. eauto.
    + simpl. eapply a_refl.
Qed.


Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp.

Notation "A <=' B" := (blessthan A B) (at level 53).
Reserved Notation "B ={ State }=> B'" (at level 61).

Inductive beval : BExp -> State -> BExp -> Prop :=
| elessthan_1: forall a1 a2 a1' state,
    a1 =[ state ]=> a1' ->
    (a1 <=' a2) ={ state }=> a1' <=' a2
| elessthan_2: forall i1 a2 a2' state,
    a2 =[state]=> a2' ->
    (anum i1) <=' a2 ={ state }=> (anum i1) <=' a2'
| elessthan: forall i1 i2 state b,
    b = (if Nat.leb i1 i2 then btrue else bfalse) ->
    (anum i1) <=' (anum i2) ={ state }=> b
| enot : forall b b' state,
    b ={ state }=> b' ->
    (bnot b) ={ state }=> (bnot b')
| enottrue : forall state,
    (bnot btrue) ={ state }=> bfalse
| enotfalse : forall state,
    (bnot bfalse) ={ state }=> btrue
| eand_1 : forall b1 b1' b2 state,
    b1 ={state}=> b1' ->
    (band b1 b2) ={ state }=> (band b1' b2)
| eandtrue : forall b2 state,
    (band btrue b2) ={state}=> b2
| eandfalse : forall b2 state,
    (band bfalse b2) ={state}=> bfalse
where "B ={ State }=> B'" := (beval B State B').

Reserved Notation "A ={ S }>* A'" (at level 61).
Inductive beval_clos : BExp -> State -> BExp -> Prop :=
| b_refl : forall b st, b ={ st }>* b
| b_trans : forall b1 b2 b3 st,  (b1 ={st}=> b2) -> (b2 ={ st }>* b3)  -> (b1 ={ st }>* b3)
where "A ={ S }>* A'" := (beval_clos A S A').


Example beval_lessthan:
  1 +' 3 <=' 5 ={ sigma0 }>* btrue.
Proof.
  eapply b_trans.
  - eapply elessthan_1.
    eapply aadd. simpl.  eauto.
  - eapply b_trans.
    + eapply elessthan. simpl. eauto.
    + eapply b_refl.
Qed.


Inductive Stmt :=
| assignment : Var -> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| skip : Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt.

Notation "X ::= N" := (assignment X N) (at level 60).
Notation "S ;; S'" := (sequence S S')
                        (at level 63, right associativity).

Reserved Notation "Stmt -{ State }->[ Stmt' ; State' ]" (at level 65).

Inductive eval : Stmt -> State -> Stmt -> State -> Prop :=
| eassign_2: forall var a a' state,
    a =[state]=> a' ->
    (var ::= a) -{state}->[ var ::= a' ;  state ]
| eassign: forall var state state' i,
    state' = update state var i ->
    (var ::= (anum i)) -{state}->[ skip ; state']
| eseq_1 : forall s1 s1' s2 state1 state,
    s1 -{state}->[ s1' ; state1 ] ->
    (s1 ;; s2) -{state}->[ s1' ;; s2 ; state1 ]
| eseq : forall s2 state,
    (skip ;; s2) -{state}->[ s2 ; state ]
| eifthenelse_1 : forall b b' s1 s2 state,
    b ={ state }=> b' ->
    (ifthenelse b s1 s2) -{ state }->[ ifthenelse b' s1 s2 ; state ]
| eifthenelse_true : forall s1 s2 state,
    (ifthenelse btrue s1 s2) -{ state }->[ s1 ; state ]
| eifthenelse_false : forall s1 s2 state,
    (ifthenelse bfalse s1 s2) -{ state }->[ s2 ; state ]
| ewhile: forall state b s,
    (while b s) -{state}->[ ifthenelse b (s ;; while b s) skip ; state ]
where "Stmt -{ State }->[ Stmt' ; State' ]" := (eval Stmt State Stmt' State').

Reserved Notation "Stmt -{ State }>*[ Stmt' ; State' ]" (at level 65).
Inductive eval_clos : Stmt -> State -> Stmt -> State -> Prop :=
| refl : forall stmt state, stmt -{ state }>*[ stmt ; state ]
| trans : forall s1 s2 s3 state1 state2 state3 , 
    s1 -{ state1 }->[ s2 ; state2 ] ->
    s2 -{ state2 }>*[ s3 ; state3 ] ->
    s1 -{ state1 }>*[ s3 ; state3 ]
where "Stmt -{ State }>*[ Stmt' ; State' ]" := (eval_clos Stmt State Stmt' State').


Example eval_assign:
  exists sigma,
    (x ::= y +' 10) -{ sigma0 }>*[skip ; sigma] /\ sigma x = 10.
Proof.
  exists (update sigma0 x 10).
  split.
  - eapply trans.
    + eapply eassign_2.
      eapply aadd_1.
      eapply alookup.
    + eapply trans.
      apply eassign_2.
      * unfold sigma0.
        eapply aadd. trivial.
      * eapply trans.
        ** eapply eassign. eauto.
        ** eapply refl.
  - unfold update.
    simpl.
    reflexivity.
Qed.

Definition seq_pgm := (x ::= 10);;(y ::= 1).
Example eval_seq:
  exists state,
    seq_pgm -{sigma0}>*[ skip ; state ] /\ state x = 10 /\ state y = 1.
Proof.
  eexists.
  split.
  - unfold seq_pgm.
    eapply trans.
    + eapply eseq_1.
      eapply eassign.
      reflexivity.
    + eapply trans.
      eapply eseq.
      eapply trans.
      * eapply eassign.
        reflexivity.
      * eapply refl.
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
    sumpgm_1 -{sigma0 }>*[skip ; state] /\ state sum = 1.
Proof.
  eexists.
  unfold sumpgm_1.
  split.
  - eapply trans.
    eapply eseq_1.
    eapply eassign; trivial.
    eapply trans.
    eapply eseq.
    eapply trans.
    + eapply eseq_1.
      eapply eassign; trivial.
    + eapply trans.
      eapply eseq.
      eapply trans.
      eapply eseq_1.
      * eapply eassign; trivial.
      * eapply trans.
        eapply eseq.
        eapply trans.
        ** eapply ewhile.
        ** eapply trans.
           { eapply eifthenelse_1.
             eapply elessthan_1.
             eapply alookup. }
           { unfold update. simpl.
             eapply trans.
             - eapply eifthenelse_1.
               eapply elessthan_2.
               eapply alookup.
             - simpl.
               eapply trans.
               eapply eifthenelse_1.
               + eapply elessthan.
                 simpl. trivial.
               + eapply trans.
                 eapply eifthenelse_true.
                 eapply trans.
                 eapply eseq_1.
                 eapply eseq_1.
                 eapply eassign_2.
                 * eapply aadd_1.
                   eapply alookup.
                 * simpl.
                   eapply trans.
                   eapply eseq_1.
                   ** eapply eseq_1.
                      eapply eassign_2.
                      eapply aadd_2.
                      eapply alookup.
                   ** simpl.
                      eapply trans.
                      eapply eseq_1.
                      eapply eseq_1.
                      eapply eassign_2.
                      eapply aadd. simpl. reflexivity.
                      eapply trans.
                      eapply eseq_1.
                      eapply eseq_1.
                      eapply eassign. eauto.
                      eapply trans.
                      eapply eseq_1.
                      eapply eseq.
                      eapply trans.
                      eapply eseq_1.
                      eapply eassign_2.
                      eapply aadd_1.
                      eapply alookup.
                      eapply trans.
                      eapply eseq_1.
                      unfold update. simpl.
                      eapply eassign_2.
                      eapply aadd. eauto.
                      eapply trans.
                      eapply eseq_1.
                      eapply eassign.
                      simpl. eauto.
                      eapply trans.
                      eapply eseq.
                      eapply trans.
                      eapply ewhile.
                      eapply trans.
                      eapply eifthenelse_1.
                      eapply elessthan_1. eapply alookup. unfold update. simpl.
                      eapply trans.
                      eapply eifthenelse_1.
                      eapply elessthan_2. eapply alookup. unfold update. simpl.
                      eapply trans.
                      eapply eifthenelse_1.
                      eapply elessthan. simpl. reflexivity.
                      eapply trans.
                      eapply eifthenelse_false.
                      eapply refl.
           }
  - simpl. trivial.
Qed.
