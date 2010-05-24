
Require Import ZArith Wellfounded Wf_nat Arith.


Section Zad1.

  Open Scope Z_scope.
  Parameter c : Z.
  Definition R_c  (x y : Z) := c <= y /\ x < y.
  SearchAbout (Z -> nat).
  Eval compute in Zabs_nat (-4).

  (* 0 -> 1, neg -> 0, pos -> S pos*)
  Definition connat x :=
    match x - c with
      | 0 => S O
      | Zneg _ => O
      | Zpos p => S (nat_of_P p)
    end.
(*
  Lemma connat_inj : forall x y, connat x = connat y -> x -c = y -c.
  Proof.
    unfold connat;intros; destruct (x-c);destruct(y-c);auto;
      try discriminate; try omega.

    assert (nat_of_P p > 0)%nat by apply lt_O_nat_of_P.
    omega.

    assert (nat_of_P p > 0)%nat by apply lt_O_nat_of_P.
    omega.

    injection H.
    intro.
    assert (p = p0) by (apply nat_of_P_inj;auto).
    congruence.

    admit.
  Qed.

  Hint Resolve connat_inj.

  Lemma R_c_lt_pos : forall x y , 0 <= x-c < y -c -> (connat x < connat y )%nat.
  Proof.
    intros;unfold connat;
    destruct (x - c);destruct (y - c);try omega.

    assert (nat_of_P p > 0)%nat by apply lt_O_nat_of_P.
    omega.

    assert (Zneg p < 0) by apply Zlt_neg_0.
    omega.

    assert (nat_of_P p < nat_of_P p0)%nat.
      repeat rewrite Zpos_eq_Z_of_nat_o_nat_of_P in *.
      apply inj_lt_rev.
      omega.
    omega.

    assert (Zneg p0 <= Zpos p) by apply Zle_neg_pos.
    omega.

    assert (Zneg p < 0) by apply Zlt_neg_0.
    omega.
  Qed.

  Lemma R_c_lt_neg_pos :forall x y,
    x  - c < 0 <= y - c -> (connat x < connat y )%nat.
    intros;unfold connat;
    assert (x-c < y -c) by omega.
    destruct (x - c);destruct (y - c);try omega.

    assert (Zpos p > 0) by apply Zgt_pos_0.
    omega.

    assert (nat_of_P p < nat_of_P p0)%nat.
      repeat rewrite Zpos_eq_Z_of_nat_o_nat_of_P in *.
      apply inj_lt_rev.
      omega.
    omega.

    assert (Zneg p0 <= Zpos p) by apply Zle_neg_pos.
    omega.

    assert (Zneg p0 < 0) by apply Zlt_neg_0.
    omega.
  Qed.

  Hint Resolve R_c_lt_pos R_c_lt_neg_pos.
*)
  Lemma R_c_wf : well_founded R_c.
  Proof.
    apply well_founded_lt_compat with connat.
    intros.
    destruct H.
    assert (forall p, 0 < nat_of_P p )%nat by
      apply lt_O_nat_of_P.
    assert (forall p, Zneg p < 0) by
      apply Zlt_neg_0 .
    assert (forall p, 0 < Zpos p) by
      auto with zarith.
    unfold connat.
    assert (x - c < y -c ) by omega.
    remember (x-c) as xc ;remember (y-c) as yc.
    destruct yc;destruct xc;try rewrite <- Heqxc, <- Heqyc;
      try omega; auto with zarith arith.
    specialize H3 with p; omega.
    assert (nat_of_P p0 < nat_of_P p)%nat .
      repeat rewrite Zpos_eq_Z_of_nat_o_nat_of_P in *.
      apply inj_lt_rev.
      omega.
    omega.
    specialize H2 with p;omega.
    admit.
    admit.
    admit.
    admit.

    simpl.

    auto with zarith.
    simpl.
    destruct
    simpl.
    destruct H.
    assert (x - c < y -c) by omega.
    assert (0 <= x - c  \/ x - c <  0) by omega.
    destruct H2.
    assert (0 <= x - c < y -c) by omega.
    auto.
    admit.
(*
    assert (0 <= x - c  \/ x - c <  0) by omega.
    destruct H3.

    replace (connat x <= connat y)%nat with (connat x < S (connat y))%nat in *.
  assert (connat x < connat y \/ connat x = connat y)%nat by omega.
  clear H0.
  destruct H1.
  auto.
  destruct H.
  assert (x = y).
    assert (x - c = y - c)  by auto.
    omega.
  omega. *)
  Qed.

End Zad1.

Section Zad2.

  Require Import List NArith Arith.
  Open Scope N_scope.

  Notation " [ x ] " := (exist _ x _) : spec_scope.
  Notation " # t " := (proj1_sig t) (at level 60) : spec_scope.

  Open Scope spec_scope.


  Inductive sorted : list N -> Prop :=
  | sort_nil : sorted nil
  | sort_one : forall x, sorted (x::nil)
  | sort_cons : forall l x, (forall y, In y l -> x <= y) -> sorted l -> sorted (x::l).
  Hint Constructors sorted.

  Definition le_dec : forall x y, {(x ?= y) <> Gt} + {(x ?= y) = Gt}.
  decide equality.
  Defined.

  Goal forall x l, sorted (x::l) ->  forall y, In y l -> x <= y.
    intros.
    inversion H;subst.
    destruct H0;subst.
    auto.
  Qed.

  Lemma Nle_trans : forall x y z,
    x <= y -> y <= z -> x <= z.
    intros x y z.
    unfold Nle.
    repeat rewrite nat_of_Ncompare.
    repeat rewrite <- nat_compare_le.
    omega.
  Qed.

  Lemma sorted_cons : forall x y l,
    y <= x -> sorted (x::l) -> sorted (y::x::l).
    intros.
    constructor;intros;eauto;subst.
    inversion H0;subst;simpl in*;intuition;eauto;
    try rewrite <-H2;auto.

    apply Nle_trans with x;auto.
  Qed.
  Hint Resolve sorted_cons.

  Lemma sorted_mixin : forall a b c l,
    sorted (b :: c :: l) -> sorted (a :: b :: l) -> sorted (a :: b :: c:: l).
    intros.
    inversion H;simpl;intros;subst.
    inversion H0;simpl;intros;subst.
    constructor;intros;auto.
    simpl in *;intuition.
    rewrite <- H1.
    apply Nle_trans with b;intuition.
  Qed.
  Hint Resolve sorted_mixin.

  Lemma Nle_refl : forall x, x <= x.
    intros; unfold Nle.
    rewrite Ncompare_refl; intros.
    discriminate.
  Qed.
  Hint Resolve Nle_refl.

  Ltac inv_int H :=  inversion H;intros;subst;simpl in *;intuition.

  Lemma sorted_perm : forall x y xs l,
    y <= x -> sorted (y::xs) -> Permutation (x::xs) l -> sorted l -> sorted (y::l).
    intros.
    inv_int H1.
    constructor;intros;auto.
    assert (Permutation l (x::xs)) by (apply Permutation_sym;auto).
    assert (In y0 (x::xs)).
    apply Permutation_in with l ;auto.
    inv_int H0; try solve [rewrite <- H8;auto].
  Qed.
  Hint Resolve sorted_perm.

  Lemma lt_le : forall x y, x < y -> x <= y.
    intros.
    unfold "<=". unfold "<" in H.
    rewrite H. discriminate.
  Qed.

  Lemma gt_lt : forall x y, (x ?= y) = Gt -> (y ?= x) = Lt.
    intros.
    assert (CompOpp (x ?= y) = (y ?= x)).
    eauto using Ncompare_antisym.
    rewrite <- H0.
    rewrite H.
    auto.
  Qed.
  Hint Constructors Permutation.

  Definition insert : forall (l:list N) (x:N)  ,sorted l  -> {l' : list N | Permutation (x::l) l' /\ sorted l'}.
  refine (
    fix F l x{struct l} :  sorted l -> {l' : list N | Permutation (x::l) l' /\ sorted l'}  :=
      match l with
        | nil =>  fun _ => _ (x::nil)
        | y::xs => fun p => if le_dec x y then _ else _ (F xs x _ ) p
      end);intros.
  exists (x::nil).
  intuition;eauto.

  exists (x::y::xs).
  intuition;eauto.

  destruct x0.
  assert (y < x) by
    (apply gt_lt;auto).
  assert (y <= x) by
    (apply lt_le;auto).

  exists (y::x0).
  intuition;eauto.

  inversion p;eauto.
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

  Eval compute in insert (1::2::4::nil) 3 s123.

  Definition insertsort : forall l : list N,
    {l' : list N | Permutation l l' /\ sorted l'}.
  induction l;eauto.
  destruct IHl.
  destruct a0.
  specialize (insert x a H0);intros.
  destruct H1.
  exists x0.
  intuition;eauto.
  Defined.

  Eval compute in insertsort (2::5::1::6::3::nil).
End Zad2.

Section Zad3.
  Parameter A : Type.

  Section ListT.
    Inductive listT :=
    | nilT  : listT
    | consT : A -> listT -> listT.
  End ListT.

  Definition index := nat.

  Inductive expr : Set :=
  | Atom : index -> expr
  | Plus : expr -> expr -> expr .

  Definition atommap := list nat.

  Definition interp_var (i:index) (vm:atommap) := nth i vm  0.

  Fixpoint interp vm e  :=
    match e with
      | Atom i => interp_var i vm
      | Plus e1 e2 => interp vm e1  + interp vm e2
    end.

  Fixpoint flat_expr_aux e acc :=
    match e with
      | Atom i => Plus e acc
      | Plus e1 e2 => flat_expr_aux e1 (flat_expr_aux e2 acc)
    end.

  Fixpoint flat_expr e :=
    match e with
      | Atom _ => e
      | Plus e1 e2 => flat_expr_aux e1 (flat_expr e2)
    end.

  Lemma flat_aux_correct : forall vm e1 e2,
    interp vm e1 + interp vm e2 = interp vm (flat_expr_aux e1 e2).
    double induction e1 e2;intros;simpl;
    repeat match goal with
             | [ H : context [ _ = interp _ ( flat_expr_aux _ _)] |- _ ] => rewrite <- H
           end;simpl;auto with arith.
  Qed.

  Hint Rewrite <- flat_aux_correct : db .
  Lemma flat_correct : forall vm e1 e2,
    interp vm (flat_expr e1) = interp vm (flat_expr e2)
    -> interp vm e1 = interp vm e2.
    assert (forall vm e, interp vm e = interp vm (flat_expr e)) by
      (induction e; simpl; try autorewrite with db; auto).
    intros; do 2 rewrite <- H in *;trivial.
  Qed.

  Lemma interp_rev_corr : forall vm e,
    interp vm e = interp (rev vm) e.
    induction e;intros;simpl.
    admit.

    rewrite IHe1, IHe2;auto.
  Qed.
  Hint Rewrite <- interp_rev_corr : db.

  Lemma interp_rev_refl : forall vm e1 e2,
    interp (rev vm) e1 = interp (rev vm) e2
    -> interp vm e1 = interp vm e2.
    intros.
    autorewrite with db in H.
    auto.
  Qed.

  Fixpoint listT_to_atommap (lst : list nat) :=
    match lst with
      | nil => fun _ => 0
      | a :: xs => fun n =>
        match n with
          | 0 => a
          | S m => listT_to_atommap xs m
        end
    end.


  Ltac insert_atom atoms a :=
    match atoms with
      | nil => constr:(a::nil)
      | a ::  _ => atoms
      | ?x :: ?xs =>
        let ys := insert_atom xs a in
          constr:(x ::ys)
    end.

  Ltac enum_atoms atoms a :=
    match a with
      | ?e1 + ?e2 => enum_atoms ltac:(enum_atoms atoms e1) e2
      | _ => insert_atom atoms a
    end.

  Ltac enum_atom a  := enum_atoms (@nil nat) a.

  Ltac find_atom a lst :=
    match lst with
      | a ::  _ => constr: 0
      |  _ :: ?xs =>
        let n := find_atom a xs in
          constr: (S n)
    end.

  Ltac model atoms v :=
    match v with
      | (?X1 + ?X2) =>
        let r1 := model atoms X1 with r2 := model atoms X2
          in constr : (Plus r1 r2)
      | _  =>
        let n := find_atom v atoms in
          constr: (Atom n)
    end.


  Ltac prover :=
    intros;
    match goal with
      | [ |- ?X1 = ?X2] =>
        let atoms1 := enum_atom X1 in
        let atoms2 := enum_atom X2 in
          let e1 := model atoms1 X1 in
          let e2 := model atoms2 X2 in
            (change (interp atoms1 e1 =
                     interp atoms2 e2)
            ; repeat (apply flat_correct || apply interp_rev_corr ); reflexivity)
      | _ => idtac "dupa"
    end.

  Definition nmn := Plus (Atom 0) (Plus (Atom 1) (Atom 0)).
  Definition mnn := Plus (Atom 0) (Plus (Atom 1) (Atom 1)).
  Lemma refl_test : forall n m,
    n+(m+n) = m+(n+n).
    intros.
    change (interp (n::m::nil) nmn = interp (m::n::nil) mnn).
    unfold nmn,mnn.
    rewrite interp_rev_corr.
    simpl rev.
    apply flat_correct.
    change (interp (n::m::nil) (Plus (Atom 0) (Plus (Atom 1) )) = interp (y::x::nil) (Plus (Atom 0) (Atom 1))).
    prover.
    intros.
    change (interp (x::y::nil) (Plus (Atom 0) (Atom 1)) = interp (y::x::nil) (Plus (Atom 0) (Atom 1))).
    apply interp_rev_corr.
    rewrite interp_rev_corr.
    simpl.
    auto.
    reflexivity.
    auto.
    prover.
  admit.
  Qed.
  Lemma refl_test2 : forall x y z,
    x + y + z = x + (y + z).
    prover.
  Qed.
  Lemma reflection_test_norm : forall f x y z t u,
    (f x + x) + (1 + y + z + (t + u)) = f x + x + 1 + y + (z + (t + u)).
  Proof.
    prover.
  Qed.





End Zad3.