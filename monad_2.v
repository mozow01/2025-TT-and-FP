Require Import List.
Require Import Arith.
Import ListNotations.

Inductive Nev : Set :=
  | Anna : Nev
  | Bela : Nev
  | Cili : Nev
  | Dani : Nev.   

(* Egyenlőség eldönthetősége (hogy megtaláljuk a nevet a listában) *)
Theorem Nev_dec : forall n1 n2 : Nev, {n1 = n2} + {n1<>n2}.
Proof.
  induction n1,n2.
  all: tryif left; reflexivity then auto else right; discriminate.
Defined.

Fixpoint pontszam_lek (nev : Nev) (l : list (nat * Nev)) : option nat :=
  match l with 
    | [] => None
    | (pont', nev') :: l' => if Nev_dec nev' nev 
                              then Some pont' 
                              else pontszam_lek nev l'
  end.

Definition adatok := [ (45, Anna) ; (38, Bela) ; (50, Cili) ].

Eval simpl in pontszam_lek Bela adatok.

Print option.

(* MONÁD *)

(*Az option egy jó dolog a kivételek kezelésére. De ez egy általános CS dolog, az úgy nevezett Kleisli-monád.

Egy M Kleisli-monád egy Type -> Type típusú dolog, azaz típust eszik és típust ad vissza, vagyis egy polimorf típuskonstruktor, ilyen még 

  -- list, 
  -- state.

tartozik hozzá két furcsi operáció: 

  -- unit : A -> M A, az egységleképezés
  -- bind, ami egy kötő leképezés

                 unit
              A ----> M A  bind ma unit = ma  
                \      |   (bind _ unit = id)
                 \     |
                  \ f  |   bind (unit a) f = f a
                   \   |   ((bind f) o unit = f)
                unit\  |   (bind o unit) _ = Id)
              B ----> M B
                \      |
                 \     |
                  \ g  |   bind (bind ma f) g = bind ma (fun x => bind (f x) g)
                   \   |   ( bind g o bind f = bind ((bind g) o f), de f >> g -ként írja) 
                    \  |  
              C       M C
*)


Class Monad (M : Type -> Type) : Type := mk_monad
{
  (* Sort: M *)
  
  (* Műveletek *)
  bind : forall {A B : Type}, M A -> (A -> M B) -> M B;
  unit : forall {A : Type}, A -> M A;
  
  (* Komputációs rész *)
  left_id_law : forall (A B : Type) (a : A) (f : A -> M B), bind (unit a) f = f a;
  right_id_law : forall (A : Type) (ma : M A), bind ma unit = ma;
  assoc_law : forall (A B C : Type) (ma : M A) (f : A -> M B) (g : B -> M C),
                bind (bind ma f) g = bind ma (fun x => bind (f x) g)
}.

Print option. 

(* Option vagy maybe típusa: 

Inductive option (A : Type) : Type :=
    Some : A -> option A | None : option A.

műveletei: *)

Definition bind_opt {A B: Type} (ma : option A) (f : A -> option B) : option B :=
  match ma with
    | Some a => f a
    | None => None
  end.

Definition return_opt {A : Type} (a : A) : option A := Some a.

Instance OptionMonad : Monad option.
Proof.
  apply mk_monad with (bind := @bind_opt) (unit := @return_opt).
  all: intros; try destruct ma; auto.
Defined.


(* Alkamlazás *)

(* 
Feladat: Anna és Béla, mint Csipet csapat, közös pontszámának kiszámítása. 
*)

Definition AnnaBela_csapat_eredmeny (adatok : list (nat * Nev)) : option nat :=
  bind (pontszam_lek Anna adatok) (fun pont_anna =>   (* Anna adatait odaadja annak, hogy *)
    bind (pontszam_lek Bela adatok) (fun pont_bela =>   (* Bela adatait odaadja annak, hogy *)
      unit (pont_anna + pont_bela)                        (* összeadja és visszaadja *)
    )
  ).

Compute (AnnaBela_csapat_eredmeny adatok). 
(* Eredmény: Some 83 *)


(* 2. Eset: Hiányos lista (Béla lógott a vizsgáról) *)
Definition hianyos_eredmenyek := [ (45, Anna) ; (50, Cili) ].

Compute (AnnaBela_csapat_eredmeny hianyos_eredmenyek). 

(* Látszik szépen a lépcsőzetes behúzás *)
Definition harmas_csapat_eredmeny (adatok : list (nat * Nev)) : option nat :=
  bind (pontszam_lek Anna adatok) (fun p1 =>
    bind (pontszam_lek Bela adatok) (fun p2 =>
      bind (pontszam_lek Cili adatok) (fun p3 =>
        unit (p1 + p2 + p3)
      )
    )
  ).

Compute (harmas_csapat_eredmeny adatok).
(* Eredmény: Some 133 (45 + 38 + 50) *)

Definition biztonsagos_kivonas (mibol : nat) (mit : nat) : option nat :=
  if mibol <? mit 
  then None             
  else Some (mibol - mit). 
  
Definition AnnaBela_maradek (adatok : list (nat * Nev)) : option nat :=
  bind (pontszam_lek Anna adatok) (fun anna_fogyasztas =>
    bind (biztonsagos_kivonas 100 anna_fogyasztas) (fun maradek1 =>
      bind (pontszam_lek Bela adatok) (fun bela_fogyasztas =>
        bind (biztonsagos_kivonas maradek1 bela_fogyasztas) (fun maradek2 =>
          unit maradek2
        )
      )
    )
  ).
  
Compute (AnnaBela_maradek adatok).

Definition State (S A : Type) : Type := S -> (A * S).
Definition ret_s {S A} (x : A) : State S A := fun s => (x, s).
Definition bind_s {S A B} (m : State S A) (f : A -> State S B) : State S B :=
  fun s0 =>
    match m s0 with
    | (a, s1) => (f a) s1
    end.
    
Definition pop {A : Type} : State (list A) (option A) :=
  fun s => match s with | nil => (None, nil) | h :: t => (Some h, t) end.

(* Végrehajtja a pop műveletet n-szer, és összegyűjti az eredményeket. *)
Fixpoint n_pops {A : Type} (n : nat) : State (list A) (list (option A)) :=
  match n with
  | 0 => ret_s [] 
  | S n' =>
      bind_s pop (fun h_opt =>
        bind_s (n_pops n') (fun t_list =>
          ret_s (h_opt :: t_list)
        )
      )
  end. 

Compute (n_pops (A:=nat) 3) [1; 2; 3].

Print length.

Definition data := [1; 2; 3].

Compute (n_pops (A:=nat) (length data)) data.

