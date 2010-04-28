Require Import Arith Bool.


Section Zad1.
Ltac remove_nat' n :=
     repeat match goal with
              | [ n : nat |- _ ] => clear n
              | [ H : context C [n] |- _ ] => clear H
            end.

  Ltac remove_nat n :=
    match goal with
      | [ |- context [n] ] => idtac
      | _ => remove_nat' n
    end.
 (* Ltac remove_nat *)

End Zad1.

Section Zad2.

  Ltac simple_tauto := repeat
    match goal with
      | [  |- True ]       => constructor
      | [  |- _ /\ _ ]      => split
      | [  |- _ -> _ ]      => intro
      | [ H : ~?P |- ?P ]  => contradiction
      | [ H : False |- _ ] => destruct H
      | [ H : ?P |- ?P ]   => exact H
      | [ H : _ /\ _ |- _ ] => destruct H
      | [ H : _ \/ _ |- _ ] => destruct H
      | [H0 : ?P -> ?Q, H1 : ?P |- _ ] => generalize (H0 H1);clear H0;intro
    end.

  Goal forall n m p:nat,
  n = m /\ m = p -> n = p.
  Proof.
    simple_tauto.
    subst.
    auto.
  Qed.

Lemma L1: forall a b c : Prop, (a -> b) /\ (b -> c) -> (a -> c).
Proof. simple_tauto. Qed.
Lemma L2: forall a b c : Prop, (a \/ b) /\ (a -> c) /\ (b -> c) -> c.
Proof. simple_tauto. Qed.
Lemma L3: forall a b c: Prop, (a /\ (a -> c)) \/ (b /\ (b -> c)) -> c.
Proof. simple_tauto. Qed.
Lemma L4: forall a: Prop, (a \/ ~a) -> (~~a -> a).
Proof. simple_tauto. Qed.
Lemma L5: forall a b c d:Prop, a -> (a->b) -> (b->c) -> (c->d) -> (a->c) /\ (a -> d).
Proof. simple_tauto. Qed.

End Zad2.

Section Zad3.
  Require Import List.

  Ltac eadd n ls :=
    match ls with
      | nil => constr:(n :: ls)
      | n :: _ => fail 1
      | ?x::?xs => let l := eadd n xs in constr:(x::l)
    end.


  Ltac collect_nats := aux (@nil nat)
  with
    aux ns :=
    match reverse goal with
      |[ N: nat |- _ ] =>
        let ls := eadd N ns in
          aux ls
      | _ => ns
    end.


  Goal forall n m k : nat, n=m -> m=k -> n=k  -> True.
  Proof.
    intros.
    let l := collect_nats in idtac l.
    trivial.
  Qed.

End Zad3.

Section Zad4.

  Section State.

    Parameter var : Set.
    Parameter var_eq_dec : forall (n m : var) , {n = m} + {n <> m}.

    Definition state := var -> nat.

    Definition empty : state := fun _ => 0.
    Definition get (s:state) (x:var)  : nat :=  s x.
    Definition set (s:state) (v:var) (x:nat) : state := fun v' =>
      if var_eq_dec v v' then x else s v'.

    Notation "s [ v ] "  := (get s v) (at level 30).
    Notation "s [ v ]  <- x " := (set s v x) (at level 40).

  End State.


  Section Exp.

    Inductive aname : Set := minus | plus | mult.

    Inductive aexp : Set :=
     | lit : nat -> aexp
     | aop : aname -> aexp -> aexp -> aexp
     | avar : var -> aexp.

    Notation " # n " := (lit n) (at level 0).
    Notation " ! v " := (avar v) (at level 4).
    Notation "x + y " := (aop plus x y) (at level 50, left associativity).
    Notation "x * y " := (aop mult x y) (at level 40, left associativity).
    Notation "x - y " := (aop minus x y) (at level 50, left associativity).

    Fixpoint aeval (st : state) exp : nat :=
      match exp with
        | #n => n
        | !v => st v
        | e1 + e2 => (aeval st e1 + aeval st e2)%nat
        | e1 - e2 => (aeval st e1 - aeval st e2)%nat
        | e1 * e2 => (aeval st e1 * aeval st e2)%nat
      end.

    Inductive bname : Set := and | or.

    Inductive bexp : Set :=
    | btrue : bexp
    | bfalse : bexp
    | bop : bname -> bexp -> bexp -> bexp
    | bneg : bexp -> bexp
    | beq : aexp -> aexp -> bexp
    | bIsZero : aexp -> bexp.

    Notation " 0 ? x  " := (bIsZero x) (at level 37, no associativity).
    Notation " x === y " := (beq x y) (at level 50).
    Notation " ! x " := (bneg x) (at level 4).
    Notation " x & y " := (bop and x y) (at level 40, left associativity).
    Notation " x || y " := (bop or x y) (at level 50, left associativity).

    Fixpoint beval st exp : bool :=
      match exp with
        | btrue => true
        | bfalse => false
        | e1 === e2 => beq_nat (aeval st e1 ) (aeval st e2 )
        | 0 ? e1 => beq_nat (aeval st e1 ) 0
        | ! be1 => negb (beval st be1)
        | be1 || be2 =>  orb (beval st be1) (beval st be2)
        | be1 & be2 =>  andb (beval st be1) (beval st be2)
      end.
  End Exp.

  Section Stmt.

    Inductive command :=
    | skip  : command
      | ass   : var -> aexp -> command
    | seq   : command -> command -> command
    | ifc   : bexp -> command -> command -> command
    | while : bexp -> command -> command.

    Notation "v ::= e" := (ass v e)  (at level 55).
    Notation "s1 ;; s2" := (seq s1 s2) (at level 60, right associativity).

    Inductive exec : state -> command -> state -> Prop :=
    | xskip   : forall s, exec s skip s
    | xass    : forall s v e , exec s (v ::= e) (set s v (aeval s e))
    | xseq    : forall s1 s2 s s' s'', exec s s1 s' -> exec s' s2 s'' -> exec s ( s1 ;; s2) s''
    | ifc_t   : forall s1 s2 b s s' , beval s b = true -> exec s s1 s' -> exec s (ifc b s1 s2 ) s'
    | ifc_f   : forall s1 s2 b s s' , beval s b = false -> exec s s2 s' -> exec s (ifc b s1 s2) s'
    | while_f : forall s1 b s, beval s b = false -> exec s (while b s1) s
    | while_t : forall s1 b s s' s'', beval s b = true -> exec s s1 s' -> exec s' (while b s1) s'' -> exec s (while b s1) s''.


  End Stmt.

  Inductive is_not_while : command -> Prop :=
  | inwSkip : is_not_while skip
  | inwAss  : forall e v, is_not_while (ass v e)
  | inwSeq  : forall s1 s2, is_not_while s1 -> is_not_while s2 -> is_not_while (seq s1 s2)
  | inwIfc  : forall b s1 s2, is_not_while s1 -> is_not_while s2 -> is_not_while (ifc b s1 s2).

  Hint Constructors is_not_while.
  Hint Constructors exec.

  Ltac ics H := inversion H;clear H;subst.

  Lemma asdf : forall c s,  is_not_while c -> exists s', exec s c s'.
  Proof.
    induction c;intros;ics H.

    exists s;constructor.
    exists (set s v (aeval s a));auto.

    destruct IHc1 with s as [s'] ;trivial.
    destruct IHc2 with s' as [s''];trivial.
    exists s'';eauto.

    destruct IHc1 with s as [s'] ;trivial.
    destruct IHc2 with s as [s''];trivial.
    assert (beval s b = true \/ beval s b = false) by
      (destruct bool_dec with (beval s b) true;
        [ left;auto | right;apply not_true_is_false;auto]).
    destruct H1;
      [ exists s';auto | exists s''; auto].
  Qed.

  Lemma asdf2: forall c s s', exec s c s' -> c <> while btrue skip.
  Proof.
    intros;intro.
    induction H; ics H0;auto;simpl in *;discriminate.
  Qed.

  Parameter P : state -> Prop.
  Theorem while_inv :
    forall c b s s',
      (forall s s', P s -> beval s b = true -> exec s c s' -> P s')
      -> P s -> exec s (while b c) s' -> P s' /\ beval s' b = false.
  Proof.
    intros.
    remember (while b c) as C.
    induction H1;ics HeqC;auto.
    apply IHexec2; [apply H with s ;auto | auto].
    Qed.

End Zad4.