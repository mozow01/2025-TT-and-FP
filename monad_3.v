Require Import List.
Require Import Arith.
Import ListNotations.

Theorem LEM_double_neg : forall A : Prop,
  ~ ~ (A \/ ~ A).
Proof.
unfold not in *.
(* ((A -> B) -> nat ) -> nat *) 
intros.
apply H.
right.
intros.
apply H.
left.
auto.
Qed.


Theorem peirce_double_neg : forall A B : Prop,
 ~ ~ (((A -> B) -> A) -> A). 
Proof.
  unfold not in *.
  intros A B H.
  apply H.
  intros K.
  apply K.
  intros a.
  exfalso.
  apply H.
  intros L.
  exact a.
Qed.

Definition add_direct (a b : nat) : nat := a + b.

Definition add_cps {R : Type} (a b : nat) (k : nat -> R) : R := 
  k (a + b).

Compute (2 + (add_direct 2 3)).

Compute (add_cps 2 3 (fun res => 2 * res)).

Inductive Nev : Type :=
  | Anna : Nev
  | Bela : Nev
  | Cili : Nev
  | Dani : Nev.

Theorem Nev_dec : forall n1 n2 : Nev, {n1 = n2} + {n1<>n2}.
Proof.
  induction n1,n2.
  all: tryif left; reflexivity then auto else right; discriminate.
Defined.

Definition adatok := [ (45, Anna) ; (38, Bela) ; (50, Cili) ].


Fixpoint pontszam_lek_cps {Ans : Type} (nev : Nev) (l : list (nat * Nev)) 
                          (succ: nat -> Ans) (fail : Ans) : Ans :=
  match l with
  | [] => fail
  | (pont, n) :: t => 
      if Nev_dec n nev 
      then succ pont 
      else pontszam_lek_cps nev t succ fail
  end.

Compute (pontszam_lek_cps Cili adatok (fun p => p) 0).

Compute (pontszam_lek_cps Dani adatok (fun p => p) 999).


Definition Answer := nat.

Definition Cont (A : Type) := (A -> Answer) -> Answer.

Definition ret {A : Type} (x : A) : Cont A := 
  fun k => k x.

Definition bind {A B : Type} (m : Cont A) (f : A -> Cont B) : Cont B :=
  fun k => m (fun a => (f a) k).

Definition callCC {A : Type} (f : (A -> Cont A) -> Cont A) : Cont A :=
  fun k => (f (fun x => fun _ignored_continuation => k x)) k.

Fixpoint szorzas_machine (l : list nat) (exit : nat -> Cont nat) : Cont nat :=
  match l with
  | [] => ret 1
  | 0 :: _ => exit 0
  | x :: xs => bind (szorzas_machine xs exit) (fun res => ret (x * res))
  end.

Definition szorzas_engine (l : list nat) : nat :=
  (callCC (fun exit => szorzas_machine l exit)) 
  (fun n => n). 
  
  (* szorzas_engine l =
  
     (callCC (fun exit => szorzas_machine l exit)) (fun n => n) =
     
     ((fun exit => szorzas_machine l exit) (fun x => fun _ignored_continuation => k x)) (fun n => n) =
     
     ((fun exit => szorzas_machine l exit) (fun x => fun _ignored_continuation => (fun n => n) x))  =
     
     ((fun exit => szorzas_machine l exit) (fun x => fun _ignored_continuation => x)) =
     
     szorzas_machine l (fun x => fun _ignored_continuation => x) 
     
     ahol exit = (fun x => fun _ignored_continuation => x) meg van hívva, vagyis a 0 :: _ => exit 0 sorban, ott ez utóbbi miatt 
     
     exit 0 = (fun x => fun _ignored_continuation => x) 0 = 0 -t ad vissza a szorzás
     
     egyébként visszaküldi az egyel kevésbé bonyolultabb rekurzív szintre.
     
  *)

Compute (szorzas_engine [1; 2; 3; 4]). 

Compute (szorzas_engine [1; 0; 5; 6; 100]). 


Definition Answer2 := (nat * list nat)%type.

Definition Cont2 (A : Type) := (A -> Answer2) -> Answer2.

Definition ret2 {A : Type} (x : A) : Cont2 A := 
  fun k => k x.

Definition bind2 {A B : Type} (m : Cont2 A) (f : A -> Cont2 B) : Cont2 B :=
  fun k => m (fun a => f a k).

Definition callCC2 {A : Type} (f : (A -> Cont2 A) -> Cont2 A) : Cont2 A :=
  fun k => f (fun x => fun _ignored_continuation => k x) k.

Fixpoint szorzas_machine2 (l : list nat) (history : list nat) (exit : (nat * list nat) -> Cont2 (nat * list nat)) : Cont2 (nat * list nat) :=
  match l with
  | [] => ret2 (1, history) 
  
  | x :: xs => 
       let current_log := history ++ [x] in

      if Nat.eqb x 0 then
           exit (0, current_log)
      else
          bind2 (szorzas_machine2 xs current_log exit) (fun res_pair => 
          match res_pair with
          | (prod, final_log) => ret2 (x * prod, final_log)
          end)
  end.

Definition szorzas_engine2 (l : list nat) : (nat * list nat) :=
  (callCC2 (fun exit => szorzas_machine2 l [] exit)) 
  (fun result_pair => result_pair). 

Compute (szorzas_engine2 [1; 2; 3; 4]). 

Compute (szorzas_engine2 [1; 0; 5; 6; 100]).