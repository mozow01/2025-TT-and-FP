(*Házi*)

(*1. stlc.v ből


Lemma vex : forall A B : Typ, exists t, ⊢ t [:] (A ⊃ (B ⊃ A)).
Proof.
Abort.

      
Lemma currying_1 : forall A B C: Typ, exists t, ⊢ t [:] ((A ⊃ (B ⊃ C)) ⊃ ((A ∧ B) ⊃ C)).
Proof.
Abort.

Lemma currying_2 : forall A B C: Typ, exists t, ⊢ t [:] ( ((A ∧ B) ⊃ C) ⊃ (A ⊃ (B ⊃ C)) ).
Proof.
Abort.

2. sttsogat_cat.v

Lemma curry_s_1 (S : STTSOGAT) : forall A B C : Typ, (Pf A -> (Pf B -> Pf C)) -> Pf (Cnj A B) -> Pf C.

Lemma curry_s_2 (S : STTSOGAT) : forall A B C : Typ, Pf (Imp A (Imp B C)) -> Pf (Imp (Cnj A B) C).

3. 
*)

Lemma kvant_1 : forall (U : Type) (A B : U -> Prop), (forall x, A x /\ B x) <-> (forall x, A x) /\ (forall x, B x). 
Abort.

Lemma kvant_2 : forall (U : Type) (A B : U -> Prop), ((exists x, A x) \/ ~(exists x, A x)) ->  ((exists x, A x) -> ((exists x, B x))) -> (forall x, A x ->  (exists x, B x)).

