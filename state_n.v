Require Import Coq.Init.Nat.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Import ListNotations.

(* A már ismert, idiomatikus State monád definíciók *)
Definition State (S A : Type) : Type := S -> (A * S).
Definition ret {S A} (x : A) : State S A := fun s => (x, s).
Definition bind {S A B} (m : State S A) (f : A -> State S B) : State S B :=
  fun s0 =>
    match m s0 with
    | (a, s1) => (f a) s1
    end.
Definition pop {A : Type} : State (list A) (option A) :=
  fun s => match s with | nil => (None, nil) | h :: t => (Some h, t) end.


(* -- AZ ÚJ FÜGGVÉNY -- *)

(* Végrehajtja a pop műveletet n-szer, és összegyűjti az eredményeket. *)
Fixpoint n_pops {A : Type} (n : nat) : State (list A) (list (option A)) :=
  match n with
  | 0 => ret [] (* Alapeset: 0-szor pop-olunk, az eredmény egy üres lista. *)
  | S n' =>
      (* Rekurzív lépés: *)
      (* 1. Pop-olj egyszer... *)
      bind pop (fun h_opt =>
        (* 2. ...majd pop-olj n'-ször (rekurzív hívás)... *)
        bind (n_pops n') (fun t_list =>
          (* 3. ...végül fűzd össze az első pop eredményét a többivel. *)
          ret (h_opt :: t_list)
        )
      )
  end.

(* Próbáljuk ki! Vegyünk ki 5 elemet egy 3 elemű veremből. *)
Compute (n_pops (A:=nat) 5) [1; 2; 3].