Set Implicit Arguments.
Section Zad1.

  Section Tree.
    Variable A: Set.
    CoInductive ltree  :=
    | cleaf : ltree
    | cbin : A -> ltree -> ltree -> ltree .

    Definition dcopy_cbin t :=
      match t with
        | cleaf => cleaf
        | cbin x l r => cbin x l r
      end.

    Lemma dcopy_cbin_id : forall t, dcopy_cbin t = t.
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
    Ltac prove_inf := cofix H;intros;rewrite <- dcopy_cbin_id;simpl;auto with inf.
    Hint Constructors inf_branch inf_all_branch : inf.
    CoFixpoint all_nat_from n  :=
      cbin n (all_nat_from (n+1)) (all_nat_from (n+1)).
    Hint Unfold all_nat_from.

    CoFixpoint all_nat_from' n :=
      cbin n (all_nat_from' (n+1)) (@cleaf nat).
    Hint Unfold all_nat_from'.

    Definition all_nat := all_nat_from 0 .
    Definition all_nat' := all_nat_from' 0.


    Lemma k_all_inf : forall k, inf_all_branch (all_nat_from k).
    Proof. prove_inf. Qed.

    Lemma nat_all_inf : inf_all_branch all_nat.
    Proof.  apply k_all_inf.    Qed.

    Lemma k_branch_inf : forall k, inf_branch (all_nat_from k).
    Proof. prove_inf. Qed.

    Lemma nat_branch_inf : inf_branch all_nat.
    Proof. apply k_branch_inf. Qed.

    Lemma k_branch_fin : forall k, fin_branch (all_nat_from' k).
    Proof.
      intros.
      rewrite <- dcopy_cbin_id.
      simpl.
      constructor 3.
      constructor.
    Qed.

    Lemma all_branch_fin : fin_branch all_nat'.
    Proof.  apply k_branch_fin. Qed.

    Lemma k_branch_binf : forall k, inf_branch (all_nat_from' k).
    Proof. prove_inf. Qed.
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
      end); inversion hp;assumption.
    Defined.
    End htree.

    Implicit Arguments htree [A].

    Section tzip.
      Variable A : Type.
      Variable B C D : A -> Type.
      Variable f : forall x,  B x -> C x -> D x.
      Definition tzip  t ( h : htree B t)  :  htree C t -> htree D t.
      refine ( fix tzip  t ( h : htree B t)  :  htree C t -> htree D t :=
        match h in htree _ t return htree C t -> htree D t with
          | htip x a => fun h1 =>
            (match h1 in htree _ t return
               match t with
                 | tip x => B x -> htree D (tip x)
                 | _ => unit
               end with
               | htip x  b => fun a => _
               | _ => tt
             end) a
          | hbin l r xl xr => fun h1 =>
            (match h1 in htree _ t return
               match t with
                 | bin l r => (htree C l -> htree D l) -> (htree C r  -> htree D r) ->  htree D (bin l r)
                 | _ => unit
               end with
               | hbin _ _ l1 r1 => fun fl fr => hbin (fl l1) (fr r1)
               | _ => tt
             end) (tzip l xl) (tzip r xr)
        end);constructor;auto.
    Defined.
  End tzip.
End Zad2.