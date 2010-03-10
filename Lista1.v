
Section Zad1.
  Require Import Classical.
  Theorem t1 :forall A B , A -> (B -> A).
  Proof.
    intros.
    assumption.
  Qed.

  Theorem t2 : forall A B C, ( A -> ( B-> C)) -> ((A -> B) -> (A -> C)).
  Proof.
    intros.
    apply X.
    assumption.
    apply X0.
    assumption.
  Qed.

(* classic logic *)
  Theorem t3 : forall A , (~ A -> A) -> A.
  Proof.
    intros. 
    specialize (classic A). 
    intro.
    destruct H0. 
    assumption.
    apply H. 
    assumption.
  Qed.


  Theorem t4 : forall A : Prop , A -> ~ ~ A.
  Proof.
    intros.
    intro.
    apply H0.
    assumption.
  Qed.

(* classic logic *)
  Theorem t5 : forall A : Prop, ~~A -> A.
  Proof.
    intro.
    apply NNPP.
  Qed.
    
    
  Theorem t6 : forall A : Prop, ~~~A -> ~A.
  Proof.
    intros.
    intro.
    apply H.
    intro.
    apply H1.
    assumption.
  Qed.

  (* unprovable A = F, B = T *)
  Theorem t7 : forall A B : Prop, (~A -> B) -> A.
  Proof.
  Abort.

  (* classic logic *)
  Theorem t8 : forall A B : Prop, ~(A->B) -> A.
  Proof.
    intros.
    apply NNPP.
    intro.
    apply H.
    intro.
    absurd A.
    assumption.
    assumption.
  Qed.
    

  Theorem t9 : forall A B,  ((((A -> B) -> A) -> A) -> B) -> B.
  Proof.
    intros.
    apply X.
    intros.
    apply X0.
    intros.
    apply X.
    intros.
    assumption.
  Qed.

  Theorem t10 : forall A B C : Prop , (A -> B) -> (A -> ~B) -> A -> C.
  Proof.
    intros.
    absurd B.
    apply H0.
    assumption.
    apply H.
    assumption.
  Qed.
    
End Zad1.

Section Zad2.

  Parameter S T : Set.
  Parameter A : S -> T -> Prop.
  Parameter B : T -> Prop.
  Parameter C : Prop.

  (* unprovable *)
  Theorem z2t1 : (exists x:S, forall (y:T) ,A x y )-> (forall (x :S), exists y:T, A x y).
  Abort All.

  (* unprovable *)
  Theorem z2t2 : ~ (forall x:T , B x) -> (exists x:T, ~B x).
  Abort All.

  Theorem z2t3 : (exists x: T, ~ (B x)) -> ~ forall x : T , B x.
  Proof.
    intros.
    destruct H.
    intro.
    apply H.
    apply H0.
  Qed. 

  Theorem z2t4 : (~ exists x : T, B x) -> forall x : T, ~ B x.
  Proof.
    intros.
    intro.
    apply H.
    exists x.
    apply H0.
  Qed.
  
  Theorem z2t5 : (forall x : T, ~ B x) -> ~  exists x : T, B x.
  Proof.
    intros.
    intro.
    elim H0.
    assumption.
  Qed.
    
(* unprovable *)
  Theorem z2t6 : (C -> exists x : T, B x) -> exists x : T, (C -> B x).
  Abort.

  Theorem z2t7 : (exists x : T, C -> B x) -> C -> exists x : T, B x.
  Proof.
    intros.
    destruct H.
    exists x.
    apply H.
    assumption.
  Qed.
  (*  unprovable *)
  Theorem z2t8 : exists x:T , forall y:T, (B x -> B y).
  Abort.

End Zad2.

Section Zad3.
  Parameter O : Set .
  Parameter Cy Se : O -> Prop. (* Cy -> cyrulik, Se -> sewilski *) 
  Parameter G : O -> O -> Prop.
  Hypothesis a1 : forall x : O, Cy x /\ Se x -> forall y:O, G x y <-> Se y /\ ~G y y.

  Theorem z3t1 : ~ exists x : O, Cy x /\Se x.

End Zad3.


Section zad4.

  (* aby auto n nie dzialalo wystarczy predykat postaci \((^n\)((A -> A ) -> \(A )-> A)\)^n )-> A 
     \( i \) to `metanawiasy`, podniesienie do potegi k rozumiem jako k-krotna konkatenacja napisu *)
  Theorem z4t1 : forall A : Prop, ((((((((A -> A)->A) -> A ) ->A) -> A )-> A) -> A ) -> A)-> A.
  Proof.
    auto 4 ||  auto 5. (*auto 4 will fail *)
  Qed.
End Zad4.

