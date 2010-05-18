
Require Import ZArith Wellfounded Wf_nat.


Section Zad1.

  Open Scope Z_scope.
  Parameter c : Z.
  Definition R_c  (x y : Z) := c <= y /\ x < y.
  SearchAbout (Z -> nat).
  Eval compute in Zabs_nat (-4).

  Definition connat x := Zabs_nat (x-c).

  Definition R_c_lt : forall x y , 0 <= c <= x -> R_c x y -> (connat x < connat y )%nat.
  Proof.
    intros.
    destruct H0.
    assert (x - c >= 0) by omega.
    assert (y - c > 0) by omega.
    unfold connat.
    assert (x - c < y - c) by omega.
    apply Zabs_nat_lt.
    omega.
  Qed.

  Hint Resolve R_c_lt.
  (*
  Lemma R_c_Acc : forall x, Acc R_c x.
  Proof.
    constructor;intros.
    assert (0 <= c \/ c < 0) by omega.
    assert (c <= y \/ y < c) by omega.
    destruct H0.
    destruct H1.
    assert (0 <= c <= y) by auto.
    A
    rewrite(R_c_lt y x H2);intros.

    assert
    induction x;constructor;intros.
    admit.
  Qed. *)

(*  Hint Resolve R_c_Acc.
  Hint Unfold well_founded. *)

  Lemma R_c_wf : well_founded R_c.
  Proof.
    apply well_founded_lt_compat with connat.
    intros.
    assert (0 <= c \/ c < 0) by omega.
    assert (c <= x \/ x < c) by omega.
    destruct H0;destruct H1.
    assert (0 <= c <= x) by auto.
    auto.

    destruct H.
    (* x < 0 <= c <= y *)
    admit.
    (* x < c < y *)

    elimtype False.

    admit.

    elimtype False.
    admit.
  Qed.

End Zad1.

Section Zad2.

  Require Import List NArith Ndec.
  Open Scope N_scope.

  Notation " [ x ] " := (exist _ x _) : spec_scope.
  Notation " # t " := (proj1_sig t) (at level 60) : spec_scope.

  Open Scope spec_scope.
(*
  Lemma min_in_nil : forall x, forall y, In y nil -> x <= y.
    intros.
    inversion H.
  Qed.
  Definition minimum : forall (l:list N), l <> nil ->  { x : N | forall y, In y l -> x <= y }.
  refine (fun l p =>
    let fix F x l {struct l}  :=
      match l with
        | nil => _ x
        | y::xs => _ (Nmin y (#(F x xs )))
      end in
    match l with
      | nil => _
      | x::xs => F x xs
    end);admit.
  Defined.
  apply 0.
Defined.*)

  Inductive sorted : list N -> Prop :=
  | sort_nil : sorted nil
  | sort_one : forall x, sorted (x::nil)
  | sort_cons : forall l x, (forall y, In y l -> x <= y) -> sorted l -> sorted (x::l).
  Hint Constructors sorted.

  Definition le_dec : forall x y, {(x ?= y) <> Gt} + {(x ?= y) = Gt}.
  decide equality.
  Defined.


  Definition insert : forall (x:N), {l | sorted l } -> {l' : list N | sorted l'}.
  refine (
    fix F x l {struct l} :=
      match l with
        | exist nil _ => [(x::nil)]
        | exist (y::xs) p => if le_dec x y then (_ (x::y::xs) p) else ( _ y p (F x)) (*[y::#(F x (_ xs p)) ]*)
      end) ;eauto.
  Defined.

  Hint Extern 1 =>
    match goal with
      | [H : _ \/ _ |- _ ] => destruct H;subst;vm_compute;intro;discriminate
      | [H : _ = _ |- _ ] => subst;vm_compute;intro;discriminate
    end.
  Definition s24 : sorted (2::4::nil).
  constructor;intros; try destruct H;intuition.
  Qed.
  Hint Resolve s24.

  Definition s123 : sorted (1::2::4::nil).
  constructor;intros;try destruct H;intuition.
  Qed.

  Eval compute in insert 3 (exist _ (1::2::4::nil) s123).

  Definition ins_perm : forall (x:N) l l',
    Permutation l l' ->  sorted l' ->
    {lst  : list N | Permutation (x::l) lst /\ sorted lst }.

  refine (fun x l sl => _ (insert x (_ l sl) ));eauto.
  intros.
  destruct x0.
  exists x0.
  intuition.
  admit.
  Qed.

  Hint Resolve ins_perm.

  Definition insertsort : forall l : list N,
    {l' : list N | Permutation l l' /\ sorted l'}.
  refine (fix F (l:list N) : {l' : list N | Permutation l l' /\ sorted l'} :=
    match  l with
      | nil => [nil]
      | x :: xs => (_ x (F xs)) (*ins_perm x xs* (_ (F xs)) (_ (F xs)) (_ (F xs))*)
    end);eauto.
  admit.
  Qed.

  admit.
  intros.
  intros.
  admit.
  intros.
  destruct x1.