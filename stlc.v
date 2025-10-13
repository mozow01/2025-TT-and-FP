(*Curry--Howard-izomorfizmus:
      logika   =   funcionális típusos programozás 
      
      Egyszerű típuselmélet
*)

(* Γ ⊢ A *)

(* Γ ⊢ p : A, 

Γ ⊢ p : A → B, 
  
  x : A ⊢ p : B ;  ⊢ λ(x:A).p : A → B  *)

Require Import List.
Import ListNotations.

Inductive Typ : Set :=
  | At : nat -> Typ
  | Tru : Typ
  | Imp : Typ -> Typ -> Typ
  | Cnj : Typ -> Typ -> Typ.
 
  
Inductive Trm : Set :=
  | tru : Trm
  | hyp : nat -> Trm
  | lam : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm
  | cnj : Trm -> Trm -> Trm
  | proj_1 : Trm -> Trm
  | proj_2 : Trm -> Trm.
  
Definition Cntxt := list Typ.

Print nat_ind.


Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  | STT_tru : forall Γ, Tyty Γ tru Tru
  | STT_hyp0 : forall Γ A, Tyty (A :: Γ) (hyp 0) A
  | STT_hypS :
      forall Γ A B i,
      Tyty Γ (hyp i) A -> Tyty (B :: Γ) (hyp (S i)) A
  | STT_lam :
      forall Γ t A B,
      Tyty (A :: Γ) t B -> Tyty Γ (lam A t) (Imp A B)
  | STT_app :
      forall Γ t s A B,
      Tyty Γ t (Imp A B) -> Tyty Γ s A -> Tyty Γ (app t s) B
  | STT_cnj :
      forall Γ t s A B,
      Tyty Γ t A -> Tyty Γ s B -> Tyty Γ (cnj t s) (Cnj A B)
  | STT_proj1 :
      forall Γ t A B,
      Tyty Γ t (Cnj A B) -> Tyty Γ (proj_1 t) A
  | STT_proj2 :
      forall Γ t A B,
      Tyty Γ t (Cnj A B) -> Tyty Γ (proj_2 t) B.
      
Notation "Γ '⊢' t '[:]' A" := (Tyty Γ t A) (at level 70, no associativity) : type_scope.

Notation "'⊢' t '[:]' A" := (Tyty nil t A) (at level 70, no associativity) : type_scope.

Print list.

Notation "A ⊃ B" := (Imp A B) (at level 70, right associativity) :
type_scope.

Notation "A ∧ B" := (Cnj A B) (at level 70, right associativity) :
type_scope.

(*Az igaz, az igaz.*)
Lemma Native_I_combinator : forall A : Prop, A -> A.
Proof.
intro A. 
intro x.
exact x.
Show Proof.
Qed. 

(* 

x: A ⊢ x [:] A              ;   A ⊢ hyp 0 [:] A 
------------------          ; 
 x: A ⊢ x [:] A             ;
-----------------------     ;  
 ⊢  [:] (A ⊃ A)             ;     ⊢ lam A (hyp 0) [:] (A ⊃ A)

  *)

Lemma I_combinator : forall A : Typ, exists t, ⊢ t [:] (A ⊃ A).
Proof.
intros.
exists (lam A (hyp 0)).
apply STT_lam.
apply STT_hyp0.
Qed.

Lemma Native_K_combinator : forall A B, A -> B -> A.
Proof.
intros A B.
intros x.
intros y.
exact x.
Show Proof.
Defined.


(*  de Bruijn kódolás ( névtelen változók )


sin x 

x |-----> sin x 

                                           A ⊢ hyp 0 [:] A 

y: B, x: A ⊢ y [:] A              ;   [B, A] ⊢ hyp 1 [:] A  
------------------          ; 
 x: A ⊢ ? [:] B ⊃ A            ;      [A] ⊢ lam B (hyp 1) [:] B ⊃ A 
-----------------------     ;  
  ⊢ ? [:] (A ⊃ (B ⊃ A)).            ;     ⊢ lam A (lam B (hyp 1)) [:] (A ⊃ (B ⊃ A))

  *)

Lemma K_combinator : forall A B : Typ, exists t, ⊢ t [:] (A ⊃ (B ⊃ A)).
Proof.
intros A B.
exists (lam A (lam B (hyp 1))).
apply STT_lam.
apply STT_lam.
apply STT_hypS.
apply STT_hyp0.
Qed.

Lemma Native_conj_comm: forall A B : Prop, A /\ B -> B /\ A.
Proof.
intros A B. 
intro x.
destruct x as [x1 x2].
split.
exact x2.
exact x1.
Show Proof.
Qed. 



(*

x : (conj A B)  ⊢ hyp 0 [:] (conj A B)       x : (conj A B)  ⊢ hyp 0 [:] (conj A B)
-----------------------------------        -------------------------------
x : (conj A B)  ⊢  proj_2 (hyp 0) [:] B          x : (conj A B)  ⊢  proj_1 (hyp 0)  [:]  A
---------------------------------------------------------------------------------- 
x : (conj A B)  ⊢ cnj (proj_2 (hyp 0)) (proj_1 (hyp 0))  [:] (conj B A)
-----------------------    
 ⊢ (lam (conj A B) (cnj (proj_2 (hyp 0)) (proj_1 (hyp 0)))) [:] (conj A B) ⊃ (conj B A)

  *)

Lemma Cnj_comm : forall A B : Typ, exists t, ⊢ t [:] ((A ∧ B) ⊃ (B ∧ A)).
Proof.
intros.
exists (lam (Cnj A B) (cnj (proj_2 (hyp 0)) (proj_1 (hyp 0)))).
apply STT_lam.
apply STT_cnj.
apply STT_proj2 with (A:=A).
apply STT_hyp0.
apply STT_proj1 with (B:=B).
apply STT_hyp0.
Defined.


Lemma Native_S_combinator: forall A B C : Prop, (A -> B) -> ((B -> C) -> (A -> C)).
Proof.
intros A B C. 
intro x.
intro y.
intro z.
apply y.
apply x.
exact z.
Show Proof.
Qed. 

(* 
            z: A, y: (B ⊃ C), x: (A ⊃ B) ⊢ hyp 2 [:] A ⊃ B   z: A, y: (B ⊃ C), x: (A ⊃ B) ⊢ hyp 0 [:] A   
                              -------------------------------------------------------------------------
z: A, y: (B ⊃ C), x: (A ⊃ B) ⊢ hyp 1 [:] B ⊃ C    z: A, y: (B ⊃ C), x: (A ⊃ B) ⊢ app (hyp 2) (hyp 0) [:] B            
-------------------------------------------------------------------------------
z: A, y: (B ⊃ C), x: (A ⊃ B) ⊢ app (hyp 1) (app (hyp 2) (hyp 0)) [:] C       ;  
------------------------------------------------------
y: (B ⊃ C), x: (A ⊃ B) ⊢ (lam A (app (hyp 1) (app (hyp 2) (hyp 0)))) [:] (A ⊃ C)           ;  
------------------          ; 
 x: (A ⊃ B) ⊢ ? [:] (lam (B ⊃ C) (lam A (app (hyp 1) (app (hyp 2) (hyp 0))))) ((B ⊃ C) ⊃ (A ⊃ C))       ;
-----------------------     ;  
 ⊢ (lam (A ⊃ B)  (lam (B ⊃ C) (lam A (app (hyp 1) (app (hyp 2) (hyp 0)))))) [:] ((A ⊃ B) ⊃ ((B ⊃ C) ⊃ (A ⊃ C))     ;     ⊢ lam A (hyp 0) [:] (A ⊃ A)

  *)

Lemma S_combinator : forall A B C : Typ, exists t, ⊢ t [:] ((A ⊃ B) ⊃ ((B ⊃ C) ⊃ (A ⊃ C))).
Proof.
intros.
exists ((lam (A ⊃ B)  (lam (B ⊃ C) (lam A (app (hyp 1) (app (hyp 2) (hyp 0))))))).
apply STT_lam.
apply STT_lam.
apply STT_lam.
apply STT_app with (A:=B).
apply STT_hypS.
apply STT_hyp0.
apply STT_app with (A:=A).
apply STT_hypS.
apply STT_hypS.
apply STT_hyp0.
apply STT_hyp0.
Qed.

(*HF*)

Lemma vex : forall A B : Typ, exists t, ⊢ t [:] (A ⊃ (B ⊃ A)).
Proof.


      
