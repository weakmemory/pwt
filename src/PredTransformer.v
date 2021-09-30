Require Import Formula.
Import Formula.Properties.
Import Formula.Syntax.
Require Import Coq.Program.Basics.

From hahn Require Import Hahn.

Section PredTransformer.
Local Open Scope formula_scope.
Local Open Scope program_scope.

Record predTransformer (τ : Formula.t -> Formula.t) :=
  { pt_preserves_disj : forall φ ψ, τ (φ ∨ ψ) ⇔ τ φ ∨ τ ψ;
    pt_preserves_conj : forall φ ψ, τ (φ ∧ ψ) ⇔ τ φ ∧ τ ψ;
    pt_entails : forall φ ψ, φ ⊨ ψ -> τ φ ⊨ τ ψ;
  }.



Add Parametric Morphism τ (pt : predTransformer τ) : τ with signature
  Formula.equiv ==> Formula.equiv as pt_more.
Proof.
  specialize pt_entails.
  unfold "⇔" in *.
  basic_solver.
Qed.

Lemma pt_ext t t'
      (PT : predTransformer t)
      (EXT: forall x, t x ⇔ t' x) :
  predTransformer t'.
Proof.
  constructor; ins.
  all: rewrite <- !EXT.
  all: apply PT; auto.
Qed.

Lemma pt_equiv t t'
      (EQV : forall φ, t φ ⇔ t' φ) :
  predTransformer t <-> predTransformer t'.
Proof.
  split; intros HH; constructor; ins.
  all: try by (rewrite <- !EQV; apply HH).
  all: by rewrite !EQV; apply HH.
Qed.

Lemma pt_f_subst_loc x m :
  predTransformer (fun φ => Formula.subst_loc φ x m).
Proof.
  constructor; simpl; specialize Formula.Properties.equiv_refl;
    try basic_solver.
  by ins; apply entails_resp_subst_loc.
Qed.

Lemma pt_f_subst_reg x m :
  predTransformer (fun φ => Formula.subst_reg φ x m).
Proof.
  constructor; simpl; specialize Formula.Properties.equiv_refl;
    try basic_solver.
  by ins; apply entails_resp_subst_reg.
Qed.

Lemma pt_compose τ1 τ2
      (pt1 : predTransformer τ1)
      (pt2 : predTransformer τ2) :
  predTransformer (τ1 ∘ τ2).
Proof.
  unfold "∘".
  constructor; ins.
  { erewrite pt_more; [| done | by apply pt_preserves_disj].
    now erewrite pt_more; [by apply pt_preserves_disj | |]. }
  { erewrite pt_more; [| done | by apply pt_preserves_conj].
    now erewrite pt_more; [by apply pt_preserves_conj | |]. }
  repeat eapply pt_entails; auto.
Qed.

Lemma pt_conj_f_l φ :
  predTransformer (fun ψ => φ ∧ ψ).
Proof.
  constructor; ins.
  { rewrite conj_sym, disj_conj_distrib.
    now rewrite conj_sym, (conj_sym ψ φ). }
  { now rewrite
      <- (conjA _ φ ψ),
      (conj_sym _ φ),
      <- (conjA _ φ),
      <- equiv_conj_idemp,
      conjA. }
  now apply entails_conj.
Qed.

Lemma pt_conj_f_r φ :
  predTransformer (fun ψ => ψ ∧ φ).
Proof.
  erewrite pt_equiv.
  { eapply pt_conj_f_l. }
  ins. apply conj_sym.
Qed.

Lemma pt_disj φ :
  predTransformer (fun ψ => φ ∨ ψ).
Proof.
  constructor; ins.
  { now rewrite
      <- (disjA _ φ ψ),
      (disj_sym _ φ),
      <- (disjA _ φ),
      equiv_disj_idemp,
      disjA. }
  { rewrite <- disj_sym, conj_disj_distrib.
    apply conj_more; apply disj_sym. }
  now apply entails_resp_disj.
Qed.

Lemma pt_taut_impl_impl τ χ φ ψ
      (PT   : predTransformer τ)
      (TAUT : Formula.tautology (τ χ)) :
  τ ((χ ⇒ φ) ⇒ ψ) ⇔ τ (φ ⇒ ψ).
Proof.
  unfold "⇒".
  rewrite !pt_preserves_disj; auto.
  erewrite pt_more with (x := ¬ ((¬ χ) ∨ φ)); [| done |].
  2: now rewrite formula_de_morgan, elim_dneg.
  rewrite pt_preserves_conj, pt_preserves_disj; auto.
  apply equiv_true_taut_l in TAUT.
  now rewrite <-TAUT, conj_true_l.
Qed.

Lemma impl_preserves_pt τ ϕ
      (PT   : predTransformer τ) :
  predTransformer (fun ψ => ϕ ⇒ τ ψ).
Proof.
  eapply pt_compose; auto.
  apply pt_disj.
Qed.

Lemma conj_l_preserves_pt τ ϕ
      (PT   : predTransformer τ) :
  predTransformer (fun ψ => ϕ ∧ τ ψ).
Proof.
  eapply pt_compose with (τ1 := Formula.conj ϕ) ; auto.
  apply pt_conj_f_l.
Qed.

Lemma conj_r_preserves_pt τ ϕ
      (PT   : predTransformer τ) :
  predTransformer (fun ψ => τ ψ ∧ ϕ).
Proof.
  eapply pt_compose with (τ1 := fun x => x ∧ ϕ) ; auto.
  apply pt_conj_f_r.
Qed.


Lemma pt_split_world χ τ
      (PT1 : predTransformer (fun x => χ ⇒ τ x))
      (PT2 : predTransformer (fun x => (¬ χ) ⇒ τ x)) :
  predTransformer τ.
Proof.
  Local Ltac specializer :=
    repeat (
        match goal with
        | locf : _, regf : _, eregf : _, qf : _,
          PT : _ ⊨ _ |- _ => specialize (PT locf regf eregf qf)
        end).
  constructor; ins.
  1: eapply pt_preserves_disj with (φ := φ) (ψ := ψ) in PT1;
    eapply pt_preserves_disj with (φ := φ) (ψ := ψ) in PT2.
  2: eapply pt_preserves_conj with (φ := φ) (ψ := ψ) in PT1;
    eapply pt_preserves_conj with (φ := φ) (ψ := ψ) in PT2.
  3: eapply pt_entails with (φ := φ) (ψ := ψ) in PT1;
    eapply pt_entails with (φ := φ) (ψ := ψ) in PT2; auto.
  1-2:
    destruct PT1 as [PT11 PT12];
    destruct PT2 as [PT21 PT22];
    split; ins.
  all: do 4 intro; specializer.
  all: unfold "⊨", implb in *; simpls; unfold negb, "||" in *.
  all: ins; desf.
Qed.


Lemma pt_conj_impl  φ ψ t1 t2
      (PT1 : predTransformer t1)
      (PT2 : predTransformer t2)
      (DISJ : ~ Formula.satisfiable (φ ∧ ψ)) :
  predTransformer (fun x => (φ ⇒ t1 x) ∧ (ψ ⇒ t2 x)).
Proof.
  apply pt_split_world with (χ := φ).
  { eapply pt_equiv with (t' := fun _ => _).
    { ins.
      rewrite impl_as_disj_remember,
              conj_spread,
              conj_impl_weaker_premise,
              conj_impl_disjunctive_premise at 1; auto.
      { easy. }
      now eapply entails_impl with (φ := φ). }
    now apply impl_preserves_pt,
              conj_r_preserves_pt,
              conj_l_preserves_pt. }
  eapply pt_equiv with (t' := fun _ => _).
  { ins.
    rewrite impl_as_disj_remember,
            conj_spread,
            conj_impl_disjunctive_premise at 1; auto.
    { easy. }
    rewrite <- elim_dneg.
    apply taut_equiv_not_satisfiable_neg.
    rewrite formula_de_morgan2, elim_dneg.
    apply formula_lem. }
  now apply impl_preserves_pt,
            conj_l_preserves_pt,
            conj_l_preserves_pt,
            impl_preserves_pt.
Qed.

Lemma conj_list_pt {A} (l : list A) φ τ
      (DISJ : ForallPairs (fun i j => Formula.satisfiable (φ i ∧ φ j) -> i = j) l)
      (PT : Forall (fun i => predTransformer (τ i)) l) :
  predTransformer (fun x => Formula.conj_list (map (fun i => φ i ⇒ τ i x) l)).
Proof.
  induction l; ins; desf.
  apply pt_split_world with (χ := φ a).
  2: { eapply pt_equiv with (t' := fun _ => _).
       { ins.
         rewrite impl_as_disj_remember,
         conj_spread,
         conj_impl_disjunctive_premise at 1; auto; try easy.
         apply taut_equiv_not_satisfiable_neg.
         rewrite elim_dneg. apply formula_lem. }
       apply impl_preserves_pt,
             conj_l_preserves_pt,
             conj_l_preserves_pt.
       apply IHl.
       { unfold ForallPairs; ins.
         apply DISJ; basic_solver. }
       inv PT. }
  eapply pt_equiv with (t' := fun x => φ a ⇒ (φ a ⇒ τ a x)).
  2: { do 2 apply impl_preserves_pt. inv PT. }
  ins.
  rewrite impl_conj_r.
  split; [now apply entails_elim_conj_l1|].
  apply entails_elim_conj_r; split; try easy.
  clear IHl. induction l; ins.
  { red_helper; ins; desf. }
  rewrite impl_conj_r.
  apply entails_elim_conj_r. split.
  2: { apply IHl.
       { red; ins; apply DISJ; auto; desf; try by repeat constructor. }
       eapply incl_Forall; eauto. 
       red; ins; desf; auto. }
  red_helper; ins; desf.
  enough (a = a0); subst; try easy.
  apply DISJ; try by repeat constructor.
  apply sat_iff. repeat eexists; ins.
  now rewrite Heq3, Heq2.
Qed.

End PredTransformer.
