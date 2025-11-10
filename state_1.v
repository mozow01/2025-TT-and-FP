(* A korábbi monadikus definíciók emlékeztetőül *)
Require Import Coq.Init.Nat.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Import ListNotations.

Definition State (S A : Type) : Type := S -> (A * S).
Definition ret {S A} (x : A) : State S A := fun s => (x, s).
Definition bind {S A B} (m : State S A) (f : A -> State S B) : State S B :=
  fun s0 =>
    match m s0 with
    | (a, s1) => (f a) s1
    end.
Definition pop {A : Type} : State (list A) (option A) :=
  fun s => match s with | nil => (None, nil) | h :: t => (Some h, t) end.


(* -- A hibás példa -- *)

(* 1. Egy NEM monadikus pop, ami csak egy sima függvény *)
Definition pop_manual {A : Type} (current_stack : list A) : option A * list A :=
  match current_stack with
  | nil => (None, nil)
  | h :: t => (Some h, t)
  end.

(* 2. Két pop végrehajtása manuálisan, de HIBÁSAN *)
Definition two_pops_manual_HIBAS {A : Type} (initial_stack : list A)
  : (option A * option A) * list A :=
  (* Első pop az eredeti veremmel *)
  match pop_manual initial_stack with
  | (val1, stack1) =>
      (* Második pop, de véletlenül újra az EREDETI veremmel! *)
      match pop_manual initial_stack with (* <-- ITT A HIBA! `stack1` kellene *)
      | (val2, stack2) =>
          ((val1, val2), stack2)
      end
  end.

(* 3. Futtassuk a hibás kódot *)
Compute two_pops_manual_HIBAS [10; 20; 30].


(* Két elem kivétele a veremből a monád segítségével *)
Definition two_pops {A : Type} : State (list A) (option A * option A) :=
  bind pop (fun first_val =>
    bind pop (fun second_val =>
      ret (first_val, second_val)
    )
  ).

(* Futtassuk a monadikus, helyes kódot *)
Compute (two_pops (A:=nat)) [10; 20; 30].