


(*

A -> B          A
---------------------------
         B
         
         
        A |- B
-----------------------------
         |- A -> B
         
         
A                       B
---------------------------
            A/\B
            
            
            A/\B
-------------------------
             A
             
            A/\B
------------------------
             B


*)


Theorem problem_1 : forall A : Prop, A -> A.
Proof.
intros.
exact H.
Qed.

Theorem problem_2 : forall A B : Prop, A/\B -> B/\A.
Proof.
intros.
split.
 -
destruct H as [H1 H2].
exact H2.
 -
destruct H as [H1 H2].
exact H1.
Show Proof.
Eval cbn in ((fun (A B : Prop) (H : A /\ B) =>
 conj
   match H with
   | conj x x0 => (fun (_ : A) (H2 : B) => H2) x x0
   end
   match H with
   | conj x x0 => (fun (H1 : A) (_ : B) => H1) x x0
   end)). 
Qed.

(*

(C^B)^A = C^(B * A)



Theorem problem_3 : forall A B C : Prop, (A -> (B -> C)) -> (A /\ B -> C). 
Proof.
*)

Theorem problem_2_1 : forall A B : Prop, A/\B -> B/\A.
Proof.
intros.
induction H.
Print sum_rect.
exact (conj H0 H).
Show Proof.
Qed.


