
(*

   A_i
------------ left i=1; right i=2.
A_1 \/ A_2

              A     B
              .     .
  H: A \/ B   C     C
--------------------  destruct H as [H1 | H2]
        C
        
        

*)


Lemma problem_1 : forall (A B C : Prop), A /\ (B \/ C) -> (A /\ B) \/ (A /\ C). 
Proof.
intros.
destruct H as [H1 H2].
destruct H2.
 - left. auto.
 - right. Print and. exact (conj H1 H). 
Qed.

(* C^A * C^B = C^(A+B)  *)

Lemma problem_2 : forall (A B C : Prop), ((A \/ B) -> C) -> (A -> C). 
Proof.
intros.
apply H. 
left.
exact H0.
Qed.

Print or.

Print not.

Print False_ind.

Lemma problem_3 : forall (A B : Prop), (~ A \/ B) -> (A -> B). 
Proof.
intros.
inversion H.
 - contradiction.
 - auto.
Qed.

Lemma problem_4 : forall (A B : Prop), (A \/ ~ A) -> (A -> B) -> (~ A \/ B). 
Proof.
intros.
destruct H.
 - auto.
 - left; exact H.
Qed.

Lemma problem_5 : forall (A : Prop), ~ ~ (A \/ ~ A). 
Proof.
intros.
unfold not in *.
intros.
apply H.
right.
intros.
apply H.
left.
exact H0.
Qed.


(*

   A t 
---------------
(exists (x : U), A x)

(exists (x : U), A x)    forall x: U, A x -> C
----------------------------------------
                      C

*)


Lemma problem_6 : forall (U : Type) (A B : U -> Prop), (exists (x : U), A x /\ B x) -> (exists (x : U), A x) /\ (exists (x : U), B x). 
Proof.
intros.
split.
destruct H.
exists x.
intuition.
destruct H.
exists x.
intuition.
Qed.

Print inhabited.

Lemma drinker_dual : forall (U : Type) (A : U -> Prop), 
((exists (y : U), A y) \/ ~ (exists (y : U), A y)) ->
(inhabited U) ->  
(exists (x : U), (exists (y : U), A y) -> A x). 
Proof.
intros.
inversion H.
destruct H as [K | L].
inversion K.
exists x.
intuition.
inversion H0.
exists X.
intros.
contradiction.
inversion H0.
exists X.
intros.
contradiction.
Qed.

  