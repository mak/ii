
Section Zad3.

  Variable A : Type.
  
  Definition num : (A -> A) -> A -> A  := fun(f:A->A) (x:A) => f x.
 
  Fixpoint nat2num (n:nat)  :=
    match n with
      | 0 => fun (f:A->A) (x:A) => x
      | S n => fun (f:A->A) (x:A) => f (nat2num n f x)
    end.

  Definition succ n := fun (f:A -> A ) (x:A) => f (n f x).


  Lemma succ_is_corrent : forall n:nat, succ (nat2num n) = nat2num(n+1).
  Proof.
    intros.
    induction n.
    simpl.
    unfold succ.
    reflexivity.
    simpl.
    unfold succ.
    unfold nat2num;fold nat2num.
    unfold succ in IHn;fold succ in IHn.
    rewrite <- IHn.
    reflexivity.
  Qed.
  Definition add (n m : (A -> A) -> A ->A ) := fun (f:A -> A) (x:A) => n f (m f x).

  Lemma add_is_correct : forall n m:nat, add (nat2num n) (nat2num m) = nat2num (n+m).
  Proof.
    intros.
    induction n.
    simpl.
    unfold add;fold add.
    induction m.
    simpl.
    reflexivity.
    unfold nat2num;fold nat2num.
    reflexivity.
    unfold add.
    unfold nat2num;fold nat2num.
    unfold add in IHn.
    simpl.
    rewrite <- IHn.
    reflexivity.
  Qed.

  Definition mul (n m : (A -> A) -> A -> A) := fun (f:A -> A) (x:A) => n (m f ) x. 

  Lemma add_mul : forall n m : nat, mul (nat2num (S n)) (nat2num m) = add (nat2num m) (mul (nat2num n) (nat2num m)).
  Proof.
    intros.
    simpl.
    unfold mul.
    unfold add.
    reflexivity.
  Qed.

  Lemma add_mult : forall n m : nat, add (nat2num m) (nat2num (n * m)) = nat2num (m + n * m ).
  Proof.
    intros.
    rewrite <- add_is_correct.
    reflexivity.
  Qed.

  Lemma mul_is_correct: forall n m: nat, mul (nat2num n) (nat2num m) = nat2num(n*m).
  Proof.
    intros.
    induction n.
    simpl.
    unfold mul;fold mul.
    reflexivity.
    unfold mult;fold mult.
    rewrite <- add_mult.
    rewrite add_mul.
    rewrite IHn.
    reflexivity.
  Qed.

End Zad3.



Section Zad4.
  
  Variable A : Type.

  Inductive list : Type  := 
   | nil : list
   | cons : A -> list -> list.


  Fixpoint nth (l : list) (n : nat) : option A :=
    match n,l with
      | 0, cons x xs  => Some x 
      | S n, cons _ xs  => nth xs n
      | _, _ => None
    end.

  Fixpoint length (l:list) : nat :=
    match l with
      | nil => 0
      | cons _ xs => 1 + length xs
    end.



  Lemma nth_in : forall (n:nat) (l:list), n < length l -> exists a: A, nth l n = Some a.
  Proof.
    Require Import Le. 
    (* nie ma co pisac trywialnych fatow dla <= *)
    unfold lt.
    induction n.
    (* base case n = 0*)
    intro.
    destruct l.
    (* rozbijamy liste*)
    simpl.
    specialize (le_Sn_O 0). 
    (* dodaj do zalozen ze ~ (1<= 0) *)
    intros.
    contradiction.
    (* koniec przypadku dla l = nil, sprzecznosc z zalozeniem o n
       mniejszym niz dlugosc listy *)
    intro.
    exists a.
    simpl.
    reflexivity.
    (* krok indukcyjny, n = S m *)
    intros.
    destruct l.
    (* rozbijamy liste, l = nil *)
    simpl.
    simpl in H.
    specialize (le_Sn_O (S n)).
    intro.
    contradiction.
    (* to samo co poprzednio *)
    simpl.
    apply IHn.
    simpl in H.
    apply (le_S_n (S n) (length l)).
    assumption.
  Qed.

End Zad4.

Section Zad5.

  Require Import EqNat.
  Require Import Bool.

  Inductive btree : Set :=
   | leaf : btree
   | node : nat -> btree -> btree -> btree.

  Fixpoint haveO (t : btree) : bool :=
    match t with 
      | leaf => false
      | node n t1 t2 => ifb (beq_nat n 0) true (orb (haveO t1)  (haveO t2))
    end.

  Inductive bbtree : Set :=
  | bleaf : bbtree 
  | bnode : nat -> (bool -> bbtree) -> bbtree.


  Fixpoint bhaveO (t : bbtree) : bool :=
    match t with
      | bleaf => false
      | bnode n ft => ifb (beq_nat n 0) true (orb (bhaveO (ft false) ) (bhaveO (ft true)))
    end.


  Fixpoint conv2 (t : bbtree) : btree :=
    match t with
      | bleaf => leaf
      | bnode n ft => node n (conv2 (ft true)) (conv2 (ft false))
    end.


  Fixpoint conv1 (t:btree) : bbtree :=
    match t with
      | leaf => bleaf
      | node n t1 t2 => bnode n (fun(b:bool) => if b then conv1 t1 else conv1 t2)
    end.


  Lemma conv2_conv1_id : forall b:btree, conv2(conv1 b) = b.
  Proof.
    intros.
    induction b.
    simpl.
    reflexivity.
    simpl.
    rewrite IHb1.
    rewrite IHb2.
    reflexivity.
  Qed.

  Lemma conv1_conv2_id : forall b:bbtree, conv1(conv2 b) = b.
  Proof.
    intros.
    induction b.
    simpl.
    reflexivity.
    simpl.
    rewrite H.
    rewrite H.
    replace b with (fun b0: bool => if b0 then b true else b false).
    reflexivity.
    transitivity 