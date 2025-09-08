From Hammer Require Import Hammer.

Class ExtensionalMartinLofTypeTheory := mk_ExtensionalMartinLofTypeTheory {
  Ty : Type; 
  Tm : Ty -> Type;

  Pi : forall (A : Ty), (Tm A -> Ty) -> Ty;

  Id : forall (A : Ty) (x y : Tm A), Ty;

  lam : forall A (B : Tm A -> Ty),
    (forall (x : Tm A), Tm (B x)) -> Tm (Pi A B);
  app : forall A (B : Tm A -> Ty),
    Tm (Pi A B) -> forall (x : Tm A), Tm (B x);

  refl : forall A (x y : Tm A), 
    x = y -> Tm (Id A x y);
  
  equality_reflection : forall A (x y : Tm A), 
    Tm (Id A x y) -> x = y;

  beta_Pi : forall A B f,
    app A B (lam A B f) = f;

  eta_Pi : forall A B t,
    lam A B (app A B t) = t;

  beta_Id : forall A (x y : Tm A) t, 
    refl A x y (equality_reflection A x y t) = t;

  eta_Id : forall A (x y : Tm A) p, 
    equality_reflection A x y (refl A x y p) = p}.

(* Feltételezzük a te teljes Class definíciódat, beleértve a beta_Id-t. *)
Context {emltt : ExtensionalMartinLofTypeTheory}.

(*Lehet benne LOGIKÁT csinálni*)

Notation "A → B" := (Pi A (fun _ => B)) (at level 40, no associativity) : type_scope.

Lemma I_combi : forall (A : Ty), Tm (A → A).
Proof.
intros.
apply lam.
auto.
Defined.

Lemma K_combi : forall (A B : Ty), Tm (
  Pi A (fun _ => 
    Pi B (fun _ =>
      A))).
Proof.
intros.
apply lam.
intros.
apply lam.
intros.
auto.
Defined. 

Lemma I_combi_1 : forall (A : Ty), Tm ((A → A) → (A → A)).
Proof.
intros.
apply lam.
intros.
exact x.
Show Proof.
Defined. 

(*Kvantorok és egyenlőség*)

Lemma sym_ver_1 (A : Ty) (x y : Tm A) : Tm (Id A x y) -> Tm (Id A y x).
Proof.
  intros p.
  assert (H : x = y).
  apply equality_reflection.
  exact p.
  subst y.
  exact p.
Defined.

Definition sym_type_1 (A : Ty) : Ty :=
  Pi A (fun x =>
    Pi A (fun y =>
      Pi (Id A x y) (fun _ => Id A y x)
    )
  ).

Definition sym_type_2 (A : Ty) : Ty :=
  Pi A (fun x =>
    Pi A (fun y =>
      (Id A x y) → (Id A y x)
    )
  ).

Example sym_type_3 (A : Ty) : sym_type_1 A = sym_type_2 A.
Proof.
unfold sym_type_1, sym_type_2.
reflexivity.
Defined.

Lemma sym_ver_2 (A : Ty) : Tm (sym_type_2 A).
Proof. 
  unfold sym_type_2.
  apply lam.
  intros.
  apply lam.
  intros.
  apply lam.
  intros H.
  apply sym_ver_1.
  exact H.
Defined.

Example fuggveny_kongruencia : forall (A : Type) (B : A -> Type)
  (f g : forall x : A, B x) (a : A),
  f = g -> f a = g a.
Proof. 
intros.
subst f.
reflexivity.
Defined.

(* Mire jók az egyenlőségek? Pl. bizonyításegyenlőség igazolására *)


Lemma I_combi_2 : forall (A : Ty), Tm ((A → A) → (A → A)).
Proof.
  intros.
  apply lam. intro f.
  apply lam. intro x.
  exact (app A (fun _ => A) f x).
Defined.

Section FunEx.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma I_combi_3 : forall (A : Ty), I_combi_1 A = I_combi_2 A.
Proof.
intros.
unfold I_combi_1, I_combi_2.
f_equal.
extensionality x.
symmetry.
apply eta_Pi.
Defined.

Theorem funext_is_provable_in_EMLTT :
  forall A (B : Tm A -> Ty) (f g : Tm (Pi A B)),
    (forall x : Tm A, app A B f x = app A B g x) ->
    f = g.
Proof.
  intros A B f g H_pointwise_eq.
  rewrite <- (eta_Pi A B f).
  rewrite <- (eta_Pi A B g).
  f_equal.
  extensionality x.
  apply (H_pointwise_eq x).
Defined.

End FunEx.

Theorem refl_is_injective :
  forall A x y (t1 t2 : x = y),
    refl A x y t1 = refl A x y t2 -> t1 = t2.
Proof.
  intros A x y t1 t2 H_refl_eq.
  pose (H_reflected_eq := f_equal (@equality_reflection emltt A x y) H_refl_eq).

  rewrite (eta_Id A x y t1) in H_reflected_eq.
  rewrite (eta_Id A x y t2) in H_reflected_eq.

  exact H_reflected_eq.
Defined.

Section Uniqueness_of_identity_proofs.

Axiom UIP : forall (A : Type) (x y : A), forall (p q : x = y), p = q.

Theorem eta_Id_is_provable_via_Coq_UIP :
  forall A x y (t : x = y), equality_reflection A x y (refl A x y t) = t.
Proof.
  intros A x y t.
  apply UIP.
Defined.

Require Import Coq.Logic.ProofIrrelevance.

Theorem UIP_is_provable_in_EMLTT :
  forall A x y (p q : Tm (Id A x y)), p = q.
(*Vagyis feltéve a ProofIrrelevance-ot a Coq-ban minden Ty egy h-set.*)
Proof.
  intros A x y p q. 
  rewrite <- (beta_Id A x y p).
  rewrite <- (beta_Id A x y q).
  f_equal.
  apply UIP. 
Defined.

Theorem K_rule_is_provable :
  forall (A : Ty) (x : Tm A) (p : Tm (Id A x x)),
    p = refl A x x (eq_refl x).
Proof.
  intros A x p.
  apply UIP_is_provable_in_EMLTT.
Defined.


End Uniqueness_of_identity_proofs.

Section Direct_model_of_EMLTT.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.Logic.ProofIrrelevance.

Instance Coq_as_EMLTT_model : ExtensionalMartinLofTypeTheory.
Proof.
  apply mk_ExtensionalMartinLofTypeTheory with (Ty := Type) (Tm := fun T : Type => T) (Pi:=(fun A B => forall (x : A), B x)) (Id := (fun A x y => x = y)) (lam := (fun A B f => f)) (app := (fun A B f x => f x)) (refl := (fun A x y H => H)) (equality_reflection := (fun A x y p => p)). 
(* all: hammer. *)
  - (* beta_Pi: app (lam f) = f  <-->  (fun x => f x) = f *)
    intros A B f. extensionality x. reflexivity.
  - (* eta_Pi: lam (app t) = t  <-->  lam (fun x => t x) = t *)
    intros A B t. extensionality x. reflexivity.
  - (* beta_Id: refl (eq_refl t) = t *)
    intros A x y t. apply proof_irrelevance.
  - (* eta_Id: eq_refl (refl p) = p *)
    intros A x y p. apply proof_irrelevance.
Defined.

End Direct_model_of_EMLTT.


Class EMLTT_with_nat (emltt: ExtensionalMartinLofTypeTheory) := mk_EMLTT_with_nat 
{ Nat : Ty;
  zero : Tm Nat;
  succ : Tm Nat -> Tm Nat;
  nat_ind :
    forall
      (P : Tm Nat -> Ty)           
      (p_zero : Tm (P zero))       
      (p_succ : forall (k : Tm Nat), Tm (P k) -> Tm (P (succ k))), 
      forall (n : Tm Nat), Tm (P n);
  nat_beta_zero : forall P p_zero p_succ,
    nat_ind P p_zero p_succ zero = p_zero;
  nat_beta_succ : forall P p_zero p_succ n,
    nat_ind P p_zero p_succ (succ n) = p_succ n (nat_ind P p_zero p_succ n)}.





