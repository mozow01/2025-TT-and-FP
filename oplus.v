
Inductive Tree : Type :=
  | leaf : Tree
  | node (l : Tree) (r : Tree).

Inductive Oplus_type : Tree -> Tree -> Tree -> Prop :=
  | Oplus_type_leaf (s : Tree) :
      Oplus_type leaf s (node leaf s)
  | Oplus_type_node (l r r_res s : Tree) :
      Oplus_type r s r_res ->
      Oplus_type (node l r) s (node l r_res).

Theorem Oplus_sigma : forall (t s : Tree),
  { t_res : Tree | Oplus_type t s t_res }.
Proof.
  induction t.
  { 
    intros s.
    exists (node leaf s).
    apply Oplus_type_leaf.
  }

  { 
    intros s.
    destruct (IHt2 s) as [r_res H_r_res].
    exists (node t1 r_res).
    apply Oplus_type_node.
    exact H_r_res.
  }
Qed.

Theorem Oplus_uniqueness : forall (t s : Tree) (t1 t2 : Tree),
  Oplus_type t s t1 ->
  Oplus_type t s t2 ->
  t1 = t2.
Proof.
  intros t s t1 t2 H1 H2.
  (*sajnos t2-t és a tőle függőket generalizálva kell hagyni, mert H1-re akarunk indukciót*)
  generalize dependent t2.
  induction H1.
  { 
    intros t2_leaf H2_leaf.
    inversion H2_leaf.
    reflexivity.
  }
  {
    intros t2_node H2_node.
    inversion H2_node.
    subst.
    f_equal.
    apply IHOplus_type.
    exact H4.
  }
Qed.