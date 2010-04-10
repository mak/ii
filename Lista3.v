
Require Import Arith.
Require Import Bool.

Section zad1.

  
  Definition A n : nat -> nat := iter_nat n (nat -> nat) (fun f m => iter_nat m nat f (f 1)) S . 

  Lemma ack_O_m : forall m , A 0 m =  m +1.
  Proof.
    intro.
    replace (m+1) with (1 +m).
    trivial.
    apply plus_comm.
  Qed.
  
  Lemma ack_Sn_O : forall n, A (S n) 0 = A n 1.
  Proof.
    trivial.
  Qed.


  Lemma ack_sn_sm : forall n m, A (S n) (S m) = A n (A (S n) m).
  Proof.
    trivial.
  Qed.

End zad1.

Section zad2.
  


  Lemma ack_nm_gt_m: forall n m, A n m > m.
  Proof.
    intro.
    induction n.
    unfold A;simpl.
    apply gt_Sn_n.
    induction m.
    unfold A;simpl.
    apply gt_trans with 1.
    apply IHn .
    apply gt_Sn_O.
    rewrite  ack_sn_sm.
    apply gt_le_trans with (A (S n) m). 
    apply IHn.
    apply gt_le_S.
    assumption.
  Qed.
    

  Lemma ackn_Sm_m_gt : forall n m, A n (S m) > A n m. 
  Proof.
    intro.
    induction n.
    unfold A;simpl.
    intro.
    apply gt_n_S.
    apply gt_Sn_n.
    induction m.
    unfold A;simpl.
    apply ack_nm_gt_m.
    rewrite ack_sn_sm.
    apply ack_nm_gt_m.
  Qed.

Section zad3.         
 
Definition le_nat_dec (n:nat) : nat -> bool := 
  iter_nat n (nat -> bool) (fun f m=> ifb (beq_nat m 0) false (f (pred m))) (fun _  => true).

Lemma le_nat_dec_true : forall n m, le_nat_dec n m= true -> n <= m.
Proof.
  intro.
  induction n.
  intros.
  apply le_O_n.
  induction m.
  simpl.
  intro.
  discriminate H.
  unfold le_nat_dec;simpl.
  intro.
  apply le_n_S.
  apply IHn.
  assumption.
Qed.

Lemma le_nat_dec_false : forall n m, le_nat_dec n m = false -> ~(n <= m).
Proof.
  intro.
  induction n.
  intros.
  unfold le_nat_dec in H;simpl in H.
  discriminate H.
  induction m.
  intro.
  apply le_Sn_O.
  unfold le_nat_dec; simpl.
  intro.
  Lemma l : forall n m, ~(n <= m) -> ~ (S n<= S m). 
  Proof.
    auto with arith.
  Qed.
  apply l.
  apply IHn.
  assumption.
Qed.

End zad3.

Section zad4.
  
  Import Bool.
  Inductive aname : Set := minus | plus | mult.
  Inductive bname : Set := and | or.

  Inductive aexp : Set :=
   | lit : nat -> aexp
   | aop : aname -> aexp -> aexp -> aexp. 
    
     
  Inductive bexp : Set :=
   | btrue : bexp
   | bfalse : bexp
   | bop : bname -> bexp -> bexp -> bexp
   | bneg : bexp -> bexp
   | beq : aexp -> aexp -> bexp
   | bIsZero : aexp -> bexp.

  Fixpoint aeval exp : nat :=
    match exp with
      | lit n => n
      | aop name e1 e2 => match name with
                            | minus => aeval e1 - aeval e2
                            | plus => aeval e1 + aeval e2
                            | mult => aeval e1 * aeval e2
                          end
    end.

  Fixpoint beval exp : bool :=
    match exp with
      | btrue => true
      | bfalse => false
      | beq e1 e2 => beq_nat (aeval e1) (aeval e2)
      | bIsZero e1 => beq_nat (aeval e1) 0
      | bneg be1 => negb (beval be1)
      | bop name be1 be2 => match name with
                              | or => orb (beval be1) (beval be2)
                              | and => andb (beval be1) (beval be2)
                            end
    end.


  Inductive aevalR : aexp -> nat -> Prop :=
   | aeLit : forall n:nat, aevalR (lit n) n 
   | aePlus : forall e1 e2 n1 n2, 
     aevalR e1 n1 -> aevalR e2 n2 -> aevalR (aop plus e1 e2) (n1 + n2)
   | aeMult : forall e1 e2 n1 n2,
     aevalR e1 n1 -> aevalR e2 n2 -> aevalR (aop mult e1 e2) (n1 * n2)
   | aeMinus : forall e1 e2 n1 n2,
     aevalR e1 n1 -> aevalR e2 n2 -> aevalR (aop minus e1 e2) (n1 - n2).

  Inductive bevalR : bexp -> bool -> Prop :=
  | beFalse : bevalR bfalse false
  | beTrue  : bevalR btrue true
  | beEq : forall e1 e2 n1 n2, 
    aevalR e1 n1 -> aevalR e2 n2 -> bevalR (beq e1 e2) (beq_nat n1 n2)
  | beIsZero : forall e1 n1, aevalR e1 n1 -> bevalR (bIsZero e1) (beq_nat n1 0)
  | beNeg : forall e1 b1, bevalR e1 b1 -> bevalR (bneg e1) (negb b1)
  | beOr : forall e1 e2 b1 b2, 
    bevalR e1 b1 -> bevalR e2 b2 -> bevalR (bop or e1 e2) (orb b1 b2)
  | beAnd : forall e1 e2 b1 b2,
    bevalR e1 b1 -> bevalR e2 b2 -> bevalR (bop and e1 e2) (andb b1 b2).




  Lemma aeval_equiv: forall a n,aeval a = n <-> aevalR a n.
  Proof.
    intros.
    split.
    (* -> *)
    induction 1.
    induction a.
    simpl;constructor.
    induction a1.
    simpl;constructor;assumption;assumption.
    simpl;constructor;assumption;assumption.
    simpl;constructor;assumption;assumption.
    (* <- *)
    induction 1.
    simpl;reflexivity.
    simpl;rewrite IHaevalR1;rewrite IHaevalR2; reflexivity.
    simpl;rewrite IHaevalR1;rewrite IHaevalR2; reflexivity.
    simpl;rewrite IHaevalR1;rewrite IHaevalR2; reflexivity.
  Qed.

  Lemma asdf : forall a, aevalR a (aeval a).
  Proof.
    intro.
    induction a.
    simpl;constructor.
    induction a1.
    simpl;constructor;assumption;assumption.
    simpl;constructor;assumption;assumption.
    simpl;constructor;assumption;assumption.
  Qed.

  Lemma asdf2 : forall e n, aevalR e n -> aeval e = n.
  Proof.
    specialize aeval_equiv.
    intros H0 e n.
    elim H0 with e n.
    intros H1 H2.
    assumption.
  Qed.

  Lemma beval_equiv: forall a b, beval a = b <-> bevalR a b.
  Proof.
    intros.
    split.
    (* -> *)
    induction 1.
    induction a.
    simpl;constructor.
    simpl;constructor.
    induction b.
    simpl;constructor;assumption.
    simpl;constructor;assumption.
    simpl;constructor;assumption.
    simpl;constructor;apply asdf;apply asdf.
    simpl;constructor;apply asdf.
    (* <- *)
    induction 1.
    simpl;reflexivity.
    simpl;reflexivity.
    simpl;replace (aeval e1) with n1; replace (aeval e2) with n2.
    reflexivity.
    symmetry;apply asdf2;assumption.
    symmetry;apply asdf2;assumption.
    symmetry;apply asdf2;assumption.
    simpl; replace (aeval e1) with n1.
    reflexivity.
    symmetry;apply asdf2;assumption.
    simpl;rewrite IHbevalR;reflexivity.
    simpl;rewrite IHbevalR1; rewrite IHbevalR2;reflexivity.
    simpl;rewrite IHbevalR1; rewrite IHbevalR2;reflexivity.
  Qed.

End zad4.


     