Set Implicit Arguments.
Section Zad1.

  Section Tree.
    Variable A: Set.
    CoInductive ltree  :=
    | cleaf : ltree
    | cbin : A -> ltree -> ltree -> ltree .

    Definition unfold_cbin t :=
      match t with
        | cleaf => cleaf
        | cbin x l r => cbin x l r
      end.

    Lemma unfold_cbin_id : forall t, unfold_cbin t = t.
    Proof.  destruct t; simpl ; auto. Qed.

    CoInductive inf_branch : ltree -> Prop :=
    | inf_bleft :  forall x l r,
        inf_branch l -> inf_branch (cbin x l r)
    | inf_bright : forall x l r,
        inf_branch r -> inf_branch (cbin x l r).

    CoInductive inf_all_branch : ltree -> Prop :=
    | inf_all : forall x l r ,
        inf_all_branch l -> inf_all_branch r -> inf_all_branch (cbin x l r).


    Inductive fin_branch : ltree -> Prop :=
    | fin_leaf : fin_branch cleaf
    | fin_left : forall x l r, fin_branch  l -> fin_branch (cbin x l r)
    | fin_right : forall x l r, fin_branch  r -> fin_branch (cbin x l r).

    Inductive fin_all_branch : ltree -> Prop :=
    | fin_leaf2 : fin_all_branch cleaf
    | fin_all : forall x l r,
         fin_all_branch l -> fin_all_branch r -> fin_all_branch (cbin x l r).

    End Tree.

    CoFixpoint all_nat_from n  :=
      cbin n (all_nat_from (n+1)) (all_nat_from (n+1)).

    CoFixpoint all_nat_from' n :=
      cbin n (all_nat_from' (n+1)) (@cleaf nat).

    Definition all_nat := all_nat_from 0 .
    Definition all_nat' := all_nat_from' 0.


    Lemma k_all_inf : forall k, inf_all_branch (all_nat_from k).
    Proof.
      cofix H.
      intros.
      unfold all_nat_from.
      rewrite <- unfold_cbin_id.
      simpl.
      constructor;auto.
    Qed.

    Lemma nat_all_inf : inf_all_branch all_nat.
      apply k_all_inf.
    Qed.

    Lemma k_branch_inf : forall k, inf_branch (all_nat_from k).
    Proof.
      cofix H.
      intros.
      unfold all_nat_from.
      rewrite <- unfold_cbin_id.
      simpl.
      constructor.
      auto.
    Qed.

    Lemma nat_branch_inf : inf_branch all_nat.
    Proof. apply k_branch_inf. Qed.

    Lemma k_branch_fin : forall k, fin_branch (all_nat_from' k).
    Proof.
      intros.
      rewrite <- unfold_cbin_id.
      simpl.
      constructor 3.
      constructor.
    Qed.

    Lemma all_branch_fin : fin_branch all_nat'.
    Proof.  apply k_branch_fin. Qed.

    Lemma k_branch_binf : forall k, inf_branch (all_nat_from' k).
    Proof.
      cofix H.
      intros.
      rewrite <- unfold_cbin_id.
      simpl.
      constructor.
      auto.
    Qed.

End Zad1.

Section Zad2.

  Section tree.

    Variable A : Type.

    Inductive tree : Type  :=
    | bin : tree  -> tree  -> tree
    | tip : A -> tree  .
  End tree.

  Section htree .
    Variable A : Type .
    Variable B : A -> Type.

    Inductive htree :  tree A -> Type :=
    | htip : forall (x:A), B x -> htree (tip x)
    | hbin : forall (t1 t2: tree A),
        htree t1 -> htree t2 -> htree (bin t1 t2) .

    Inductive hpath (elm : A) : tree A -> Type :=
    | path_end : hpath elm (tip elm)
    | path_left : forall l r, hpath elm l -> hpath elm (bin l r)
    | path_right : forall l r, hpath elm r -> hpath elm (bin l r).

    Definition hget e t (ht : htree t) : hpath e t -> B e .
    refine (fix hget e t (ht : htree t) : hpath e t -> B e :=
      match ht in htree t return hpath e t -> B e with
        | htip x bx => fun hp =>
          match hp with
            | path_end => _
            | _ =>  tt
          end
        | hbin t1 t2 l r => fun hp =>
          (match hp in hpath _ t' return
             (match t' with
               | tip _ => unit
               | bin l r => (hpath e l -> B e) -> (hpath e r -> B e) -> B e
             end ) with
            | path_end => tt
            | path_left _ _  p => fun f  _ =>  f p
            | path_right _ _ p => fun _ f => f p
          end) (hget e t1 l) (hget e t2 r)
      end); inversion hp;trivial.
    Defined.
  End htree.

  Implicit Arguments htree [A].

  Section hlist.
    Require  Import List.
    Variable A : Type.
    Variable B : A -> Type.
    Inductive hlist : list A -> Type :=
    | hnil : hlist nil
    | hcons : forall x l' , B x -> hlist l' -> hlist (x::l').

    End hlist.
    Example heterotype : list Set := nat :: bool :: nil.

    Implicit Arguments hnil [ A B].
    Implicit Arguments hcons [A B x l'].
    Implicit Arguments hlist [A].

    Example heterolist : hlist (fun t:Set => t) heterotype :=   hcons 1 (hcons true hnil).
    Fixpoint zip A B (l1 : list A) (l2 : list B) : list (A * B) :=
      match l1,l2 with
        | x::xs,y::ys => (x,y) :: zip xs ys
        | _,_ => nil
      end.

    Fixpoint hmap A B C (ls : list A) (l : hlist B ls) (f : forall x, B x -> C x) : hlist C ls :=
      match l in hlist _ ls return hlist C ls with
        | hnil  => hnil
        | hcons x l1 a xs => hcons (f x a) (@hmap A B C l1 xs f)
      end.

    Definition hzip_with A B C (ls : list A) (hl1 hl2 : hlist B ls) (f : forall x y, B x -> B y -> C (x,y)) : hlist C (zip ls ls).
(*   match ls in list _ return hlist C (zip ls ls) with
        | nil => hnil
               (match hlist _ ( x  :: xs) return hlist C ((x,x)::zip xs xs) with
                 | hcons y _ b hl'' => hcons (a,b) (hzip A B C xs hl' hl'') *)
    induction ls;simpl.
    constructor 1.
    intros hl1 hl2.
    inversion hl1;inversion hl2;subst.
    constructor;auto.
    admit.
    auto.
  Defined.
    simpl.
    admit.


    Fixpoint hzip A B C (l : list A) (hl1 hl2 : hlist B l) : hlist C (combine l l) :=
      match hl1,hl2 in hlist _ l * hlist _ _ return hlist AB_F (combine ls ls) with
        | hcons x l1 a xs ,hcons l2 y b ys => hcons (x,y) (combine l1 l2) (a,b) (@hzip A B C l1 xs ys)
        | _,_ => hnil
      end.

Definition get_elem

  Section tzip.
    Variable A : Type.
    Variable B C D : A -> Type.
    Variable f : forall x y, B x -> C y -> D x.
    Fixpoint tzip : A B C D  (t : tree A ) : htree B t -> htree C t -> htree D t :=
      match t with
        |
  Program Fixpoint tmap (t : tree A ) (f : forall x y, B x -> C y -> D x)  (t1 : htree B t) (t2 : htree C t ): htree D t  :=
    match t1,t2 in (htree _ t * htree _ t) return htree D t with
      | hbin t1'  t2' l1 r1,hbin t1''  t2'' l2 r2 =>
        match
        hbin (tmap A B C D  _ f l1 l2) (tmap A B C D f  r1 r2)
      | htip x a,htip y b => htip (f x y a b)
      | _,_ => !
    end.



End Zad2.