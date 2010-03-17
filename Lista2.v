
Section Zad1.

  Inductive empty : Set :=
    | e : empty -> empty.

  Lemma empty_false: forall x : empty, False.
  Proof.
    intro.
    induction x.
    assumption.
  Qed.
End Zad1.

Section Zad2.

  Variable P Q R: Prop.

  Definition F : P /\ (Q \/ R) -> (P /\ Q) \/ (P  /\ R)  :=
    fun (A:P /\ (Q \/ R)) => and_ind (fun (p : P) (QR : Q \/ R) => 
      or_ind (fun q : Q => or_introl (P /\ R) (conj p q))
             (fun r : R => or_intror (P /\ Q) (conj p r))
             QR) A.
End Zad2.


Section Zad3.

  Variable A : Type.
  
  Definition num : Type :=  (A -> A) -> A -> A. 
 
  Fixpoint nat2num (n:nat) : num :=
    match n with
      | 0 => fun f x => x
      | S n => fun f x => f (nat2num n f x)
    end.

  Definition succ (n : num ):  num := fun f x => f (n f x).


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

  Definition add (n m : num )  : num := fun f x  => n f (m f x).

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

  Definition mul (n m : num ) : num := fun f x => n (m f ) x. 

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

  (* nie zbedne *)
  Axiom fun_ext : forall A B (f g : A -> B), (forall x, f x = g x ) -> f = g.
  
  
  Lemma eta_exp : forall A B (f : A -> B), f = fun x => f x.
    intros.
    apply fun_ext.
    intros.
    reflexivity.
  Qed.
  
  Lemma  b_if :forall b:bool -> bbtree, (fun b0: bool => b b0) = (fun b0 : bool => if b0 then b true else b false).
  Proof.
    intros.
    apply fun_ext.
    intro.
    destruct x.
    reflexivity.
    reflexivity.
  Qed.

  (*potrzebna ekstensjonalna rownosc funkcji, patrz askojomat wyzej*)
  Lemma conv1_conv2_id : forall b:bbtree, conv1(conv2 b) = b.
  Proof.
    intros.
    induction b.
    simpl.
    reflexivity.
    simpl.
    rewrite H;rewrite H.
    replace b with (fun b0:bool => b b0).
    rewrite <- b_if.
    reflexivity.
    symmetry.
    apply eta_exp.
  Qed.

End Zad5.

Section Zad6.

  Require Import List.
  Open Scope list_scope.

  Variable A : Type.

  Inductive tree : Type :=
  | leaf : A -> tree
  | node : nat -> (nat -> tree) -> tree. (* arnosc, funckja wyliczajaca syna *)

  Fixpoint fold_nat (B : Type )(f : nat -> B -> B)  (c : B) n := 
    match n with
      | 0   => c
      | S m => f (S m) (fold_nat B f c m)
    end.

  Fixpoint getLabel (t : tree) : list A :=
    match t with
      | leaf a => cons a nil
      | node n fc => fold_nat (list A) (fun m l => getLabel (fc m) ++ l) (getLabel (fc 0)) n
    end.

  Lemma app_non_empty : forall l1 l2 :list A, l2 <> nil -> l1 ++ l2 <> nil.
  Proof.
    intros.
    induction l1.
    simpl.
    assumption.
    simpl.
    discriminate.
  Qed.

  Lemma getLabel_non_empty : forall t:tree , getLabel t <> nil.
  Proof.
    intros.
    induction t.
    simpl.
    discriminate.
    simpl.
    induction n.
    simpl.
    intro.
    apply (H 0).
    assumption.
    simpl.
    apply app_non_empty.
    assumption.
  Qed.
End Zad6.


    


