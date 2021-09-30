From hahn Require Import Hahn.
Require Import Coq.Program.Basics.
Import ListNotations.

Set Implicit Arguments.

Section AuxDef.

Lemma restr_rel_idempotent {A} (s : A -> Prop) r :
  restr_rel s (restr_rel s r) ≡ restr_rel s r.
Proof using. basic_solver. Qed.

Lemma restr_rel2E {A} (s : A -> Prop) r : ⦗s⦘ ⨾ restr_rel s r ⨾ ⦗s⦘ ≡ restr_rel s r.
Proof using. basic_solver. Qed.

Lemma restr_rel_cr {A} (s : A -> Prop) r : restr_rel s r^? ⊆ (restr_rel s r)^?.
Proof using. basic_solver. Qed.

Section StrictPartialOrder.
Variable T : Type.

Lemma strict_partial_order_empty : @strict_partial_order T ∅₂.
Proof using. basic_solver. Qed.

Add Morphism (@strict_partial_order T) with signature
    same_relation ==> iff as strict_partial_order_more.
Proof using.
  intros x y HH. unfold strict_partial_order.
  assert (y ≡ x) as AA by (by symmetry).
  split; ins; desf; splits.
  all: try (eapply irreflexive_more; eauto).
  all: eapply transitive_more; eauto.
Qed.

End StrictPartialOrder.

Section FunctionalEquiv.
  Variables A B : Type.

  Definition func_equiv (f g : A -> B) := forall a, f a = g a.
  
  Lemma func_equiv_symmetric f g (FE : func_equiv f g) : func_equiv g f.
  Proof. unfold func_equiv in *; ins. Qed.
End FunctionalEquiv.

Definition lset {A} l x := @List.In A x l.

Lemma lset_app {A} (l l' : list A):
      lset (l ++ l') ≡₁ lset l ∪₁ lset l'.
Proof. 
  unfold lset, flip.
  by split; intro; rewrite in_app_iff.
Qed.

Lemma lset_cons {A} (l : list A) (x : A) :
  lset (x :: l) ≡₁ (eq x) ∪₁ lset l.
Proof.
  basic_solver.
Qed.

Lemma lset_empty {A} :
  (lset (@nil A)) ≡₁ ∅.
Proof.
  basic_solver.
Qed.

Lemma lset_empty_iff {A} (l : list A) :
  (lset l ≡₁ ∅) <-> l = [].
Proof.
  split.
  { induction l; auto.
    rewrite lset_cons.
    intro HH. exfalso.
    repeat (red in HH; desf).
    apply (HH a). basic_solver. }
  basic_solver.
Qed.

Lemma lset_single {A} (x : A) :
  lset [x] ≡₁ eq x.
Proof.
  basic_solver.
Qed.

Lemma lset_undup {A} (l : list A) :
  lset l ≡₁ lset (undup l).
Proof.
  unfold lset.
  by split; red; ins; apply in_undup_iff.
Qed.

Definition list_minus {A} (l l' : list A) :=
  filterP (fun x => ~ In x l') l.

Definition lset_list_minus {A} (l l' : list A) :
  lset (list_minus l l') ≡₁ lset l \₁ lset l'.
Proof.
  unfold lset, list_minus.
  unfolder; splits; intros x HH.
  { apply in_filterP_iff in HH. auto. }
  apply in_filterP_iff; desf.
Qed.

Definition list_minus_nil {A} (l : list A) :
  list_minus [] l = [].
Proof.
  basic_solver.
Qed.

Definition in_list_minus {A} (l l' : list A) (x : A) :
  List.In x (list_minus l l') <-> List.In x l /\ ~ List.In x l'.
Proof.
  unfold list_minus.
  rewrite in_filterP_iff.
  done.
Qed.

Definition filter_list_minus {A} f (l l' : list A) :
  filter f (list_minus l l') = list_minus (filter f l) (filter f l').
Proof.
  generalize dependent l'.
  induction l; ins.
  unfold list_minus in *.
  ins; desf; ins; desf; try basic_solver.
  { by rewrite IHl. }
  { exfalso.
    apply NNPP, in_filter_iff in n0. desf. }
  exfalso.
  apply NNPP in n.
  apply n0, in_filter_iff. desf.
Qed.

Lemma list_minus_cons_in {A} a (l l' : list A) (IN : In a l') :
  list_minus (a :: l) l' = list_minus l l'.
Proof. unfold list_minus; ins. desf. Qed.

Lemma list_minus_cons_nin {A} a (l l' : list A) (IN : ~ In a l') :
  list_minus (a :: l) l' = a :: (list_minus l l').
Proof. unfold list_minus; ins. desf. Qed.

Lemma lset_concat {A} (l : list (list A)) :
  lset (concat l) ≡₁ ⋃₁ x ∈ (lset l), lset x.
Proof.
  induction l; ins; desf.
  { basic_solver. }
  rewrite lset_app, IHl.
  basic_solver.
Qed.

Lemma lset_map {A B} (f : A -> B)  (l : list A) :
      lset (map f l) ≡₁ set_collect f (lset l).
Proof.
  induction l; ins.
  { rewrite !lset_empty. basic_solver. }
  now rewrite !lset_cons, IHl, set_collect_union, set_collect_eq.
Qed.

Lemma lset_filterP {A} (p : A -> Prop) (l : list A) :
  lset (filterP p l) ≡₁ lset l ∩₁ p.
Proof.
  induction l; ins; desf.
  { basic_solver. }
  all: rewrite !lset_cons, IHl; basic_solver.
Qed.

Lemma Forall2_map {A B} (R : A -> B -> Prop) (l : list A) (f : A -> B)
      (R_x_fx : forall x  (IN : In x l), R x (f x)) :
  Forall2 R l (map f l).
Proof.
  induction l; ins; desf.
  apply Forall2_cons; auto.
Qed.

Lemma Forall2_map_map {A B C} (R : B -> C -> Prop) (l : list A) f g
      (R_fx_gx : forall x  (IN : In x l), R (f x) (g x)) :
  Forall2 R (map f l) (map g l).
Proof.
  induction l; ins; desf.
  apply Forall2_cons; auto.
Qed.

Definition func_list {A B} (l : list (A * B)) :=
  forall ev ev'
    (IN : In ev l) (IN' : In ev' l)
    (EQe : fst ev = fst ev'),
    ev = ev'.

Lemma func_list_cons {A B} (a : A * B) l (FL : func_list (a :: l)) : func_list l.
Proof.
  red. ins. apply FL; auto.
  all: now apply in_cons.
Qed.

End AuxDef.

Declare Scope list_additional_scope.
Open Scope list_additional_scope.

Infix "--" := list_minus (right associativity, at level 60) : list_additional_scope.

Close Scope list_additional_scope.



(* Declare Scope auxdef_scope. *)
(* Open Scope auxdef_scope. *)

(* Notation "f ⋄ r"  := (map_rel f r) (at level 45) : auxdef_scope. *)
(* Notation "f ⋄₁ s"  := (set_map f s) (at level 39) : auxdef_scope. *)
(* Notation "⊤₂" := (fun _ _ => True) : auxdef_scope. *)
(* Notation "⊤₁" := set_full : auxdef_scope. *)

(* Close Scope auxdef_scope. *)

(* Notation "f ⋄₁ s"  := (set_map f s) (at level 39). *)
(* Notation "f □₁ s" := (set_collect f s) (at level 39). *)
(* Notation "f □ r"  := (collect_rel f r) (at level 45). *)


