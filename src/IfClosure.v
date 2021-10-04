From hahn Require Import Hahn.
From imm Require Import Events.
From imm Require Import Prog.
From imm Require Import Execution.

Require Import Pomset.
Require Import Action.
Require Import Formula.
Import Formula.Properties.
Import Formula.Syntax.
Require Import PredTransformer.
Require Import AuxDef.
Require Import AuxRel.
Require Import Language.
Require Import Semantics.
Require Import SeqBuilder.

Open Scope formula_scope.
Open Scope list_additional_scope.

(* NAME? Conditional and seq commutativity   *)
Lemma if_closure (α : thread_id) e s1 s2 s3 :
  Semantics α (Stmt.seq (Stmt.ite e s1 s2) s3) ⊆₁
  Semantics α (Stmt.ite e (Stmt.seq s1 s3) (Stmt.seq s2 s3)).
Proof.
  intros P0 PP0.
  assert (wf P0) as WF by eby eapply semantics_wf.
  inv PP0.
  inv interp1.
  rename s0 into s1.
  rename s3 into s2.
  rename s4 into s3.
  rename P1 into P12.
  rename P3 into P1.
  rename P2 into P3.
  rename P4 into P2.
  
  set (P13lambda := SeqBuilder.tlambda P1 P3).
  set (P13dep := restr_rel (events_set P1 ∪₁ events_set P3) (dep P0)).
  set (P13 := SeqBuilder.t P1 P3 P13dep
                           (restr_rel (events_set P1 ∪₁ events_set P3) (rf P0))).

  set (P23lambda := SeqBuilder.tlambda P2 P3).
  set (P23dep := restr_rel (events_set P2 ∪₁ events_set P3) (dep P0)).
  set (P23 := SeqBuilder.t P2 P3 P23dep
                           (restr_rel (events_set P2 ∪₁ events_set P3) (rf P0))).

  assert (forall d (PD1 : events_set P1 d) (PD3 : events_set P3 d),
             λ P1 d = λ P3 d) as EQLAB13.
  { ins.
    etransitivity; [|now apply (seq_label_union PE)].
    symmetry. transitivity (λ P12 d).
    { apply (seq_label_union PE). apply PE0. basic_solver. }
    now apply (if_label_union PE0). }

  edestruct SeqBuilder.props with (P1:=P1) (P2:=P3) (P12:=P13)
    as [WF1 PP13_2]; eauto; try easy. desc. unnw.

  assert (forall d (PD2 : events_set P2 d) (PD3 : events_set P3 d),
             λ P2 d = λ P3 d) as EQLAB23.
  { ins.
    etransitivity; [|now apply (seq_label_union PE)].
    symmetry. transitivity (λ P12 d).
    { apply (seq_label_union PE). apply PE0. basic_solver. }
    now apply (if_label_union PE0). }

  edestruct SeqBuilder.props with (P1:=P2) (P2:=P3) (P12:=P23)
    as [WF2 PP23_2]; eauto; try easy. desc. unnw.

  rename _EUNION  into EVENTS13.
  rename _EUNION0 into EVENTS23.
  rename _WF2 into WF3.

  assert (forall ψ, τ P1 (lset (events P12)) ψ ⇔ τ P1 (lset (events P1)) ψ) as TP1.
  { ins. apply wf_pt_family_equiv_on_E; auto.
    rewrite (events_union (if_pomset_union PE0)).
    clear. basic_solver. }

  assert (forall ψ, τ P2 (lset (events P12)) ψ ⇔ τ P2 (lset (events P2)) ψ) as TP2.
  { ins. apply wf_pt_family_equiv_on_E; auto.
    rewrite (events_union (if_pomset_union PE0)).
    clear. basic_solver. }

  assert (forall e ψ
                 (HH : events_set P1 e \/ events_set P3 e),
             τ P1 (prefix (dep P0) (eq e)) ψ ⇔ τ P1 (prefix P13dep (eq e)) ψ)
    as TP3.
  { ins. apply wf_pt_family_equiv_on_E; auto.
    subst P13dep.
    clear -HH.
    split; [|basic_solver 10].
    unfolder. ins. desc; subst.
    splits; auto. exists y, y. splits; auto. }

  assert (forall e ψ
                 (HH : events_set P2 e \/ events_set P3 e),
             τ P2 (prefix (dep P0) (eq e)) ψ ⇔ τ P2 (prefix P23dep (eq e)) ψ) as TP4.
  { ins. apply wf_pt_family_equiv_on_E; auto.
    subst P23dep.
    clear -HH.
    split; [|basic_solver 10].
    unfolder. ins. desc; subst.
    splits; auto. exists y, y. splits; auto. }
  
  assert (events_set P12 ≡₁ events_set P1 ∪₁ events_set P2) as EVENTS12
      by apply PE0.

  assert (forall d (DD : events_set P12 d),
             λ P12 d = λ P0 d) as SAMELBL_12_0.
  { symmetry. apply (seq_label_union PE); auto. }

  assert (forall d (DD : events_set P1 d),
             λ P1 d = λ P0 d) as SAMELBL_1_0.
  { ins. etransitivity; [| apply SAMELBL_12_0, EVENTS12; basic_solver].
    symmetry. apply (if_label_union PE0); auto. }

  assert (forall d (DD : events_set P2 d),
             λ P2 d = λ P0 d) as SAMELBL_2_0.
  { ins. etransitivity; [| apply SAMELBL_12_0, EVENTS12; basic_solver].
    symmetry. apply (if_label_union PE0); auto. }

  assert (forall d (DD : events_set P3 d),
             λ P3 d = λ P0 d) as SAMELBL_3_0.
  { symmetry. apply (seq_label_union PE); auto. }

  assert (forall d (DD : events_set P13 d),
             λ P13 d = λ P0 d) as SAMELBL_13_0.
  { ins. unfold SeqBuilder.tlambda. ins; desf.
    { now apply SAMELBL_1_0. }
    apply SAMELBL_3_0. apply EVENTS13 in DD. now destruct DD. }

  assert (forall d (DD : events_set P23 d),
             λ P23 d = λ P0 d) as SAMELBL_23_0.
  { ins. unfold SeqBuilder.tlambda. ins; desf.
    { now apply SAMELBL_2_0. }
    apply SAMELBL_3_0. apply EVENTS23 in DD. now destruct DD. }

  assert (forall e (P3 : lset (events P3) e)
                 (L13 :   is_r' (P13lambda e))
                 (L23 : ~ is_r' (P23lambda e)),
             False) as NR1.
  { intros e HH.
    rewrite SAMELBL_13_0; [|now apply EVENTS13; red; auto].
    rewrite SAMELBL_23_0; [|now apply EVENTS23; red; auto].
    done. }

  assert (forall e (P3 : lset (events P3) e)
                 (L13 : ~ is_r' (P13lambda e))
                 (L23 :   is_r' (P23lambda e)),
             False) as NR2.
  { intros e HH.
    rewrite SAMELBL_13_0; [|now apply EVENTS13; red; auto].
    rewrite SAMELBL_23_0; [|now apply EVENTS23; red; auto].
    done. }

  assert (forall e (P3 : lset (events P3) e)
                 (L13 : ~ is_r' (P13lambda e) \/ ~ is_r' (P23lambda e))
                 (L23 :   is_r' (λ P0 e)),
             False) as NR3.
  { intros e HH.
    rewrite SAMELBL_13_0; [|now apply EVENTS13; red; auto].
    rewrite SAMELBL_23_0; [|now apply EVENTS23; red; auto].
    ins. desf. }

  assert (forall e (P3 : lset (events P3) e)
                 (L13 : is_r' (P13lambda e) \/ is_r' (P23lambda e))
                 (L23 : ~  is_r' (λ P0 e)),
             False) as NR4.
  { intros e HH.
    rewrite SAMELBL_13_0; [|now apply EVENTS13; red; auto].
    rewrite SAMELBL_23_0; [|now apply EVENTS23; red; auto].
    ins. desf. }

  assert (rmw P0 ≡ rmw P1 ∪ (rmw P2 ∪ rmw P3)) as RMW0.
  { rewrite rmw_union with (P:=P0 ); [|by apply PE].
    rewrite rmw_union with (P:=P12); [|by apply PE0].
    now rewrite unionA. }

  assert (rmw P1 ∪ rmw P3 ⊆ restr_rel (events_set P1 ∪₁ events_set P3) (rmw P0))
    as RMW13REST.
  { rewrite (wf_rmwE_ WF1), (wf_rmwE_ WF3).
    arewrite (rmw P1 ⊆ rmw P0) by (rewrite RMW0; eauto with hahn).
    arewrite (rmw P3 ⊆ rmw P0) by (rewrite RMW0; eauto with hahn).
    basic_solver. }

  assert (rmw P2 ∪ rmw P3 ⊆ restr_rel (events_set P2 ∪₁ events_set P3) (rmw P0))
    as RMW23REST.
  { rewrite (wf_rmwE_ WF2), (wf_rmwE_ WF3).
    arewrite (rmw P2 ⊆ rmw P0) by (rewrite RMW0; eauto with hahn).
    arewrite (rmw P3 ⊆ rmw P0) by (rewrite RMW0; eauto with hahn).
    basic_solver. }

  assert (forall r,
             restr_rel (events_set P1 ∪₁ events_set P3)
                       (P13lambda ⋄ r) ≡
             restr_rel (events_set P1 ∪₁ events_set P3)
                       (λ P0 ⋄ r)) as P13λmap.
  { unfold events_set. subst P13lambda. unfold SeqBuilder.tlambda.
    ins; split.
    { unfolder; intros x y HH; desf.
      all: try (rewrite SAMELBL_1_0 in HH; [|done]).
      all: try (rewrite SAMELBL_1_0 in HH; [|done]).
      all: try (rewrite SAMELBL_3_0 in HH; [|done]).
      all: try (rewrite SAMELBL_3_0 in HH; [|done]).
      all: splits; auto. }
    unfolder; intros x y HH; desf.
    all: try (rewrite SAMELBL_1_0; [|done]).
    all: try (rewrite SAMELBL_1_0; [|done]).
    all: try (rewrite SAMELBL_3_0; [|done]).
    all: try (rewrite SAMELBL_3_0; [|done]).
    all: splits; auto. }

  assert (forall r r',
             restr_rel (events_set P1 ∪₁ events_set P3) r ∩
                       ((fun e => ifP lset (events P1) e then λ P1 e else λ P3 e) ⋄ r') ≡
             restr_rel (events_set P1 ∪₁ events_set P3) (r ∩ (λ P0 ⋄ r'))) as P13λmapAlt.
  { ins. rewrite <- inter_restr_absorb_r. unfold P13lambda in *.
    rewrite P13λmap. basic_solver 10. }

  assert (forall r,
             restr_rel (events_set P2 ∪₁ events_set P3)
                       (P23lambda ⋄ r) ≡
             restr_rel (events_set P2 ∪₁ events_set P3)
                       (λ P0 ⋄ r)) as P23λmap.
  { unfold events_set. subst P23lambda. unfold SeqBuilder.tlambda.
    ins; split.
    { unfolder; intros x y HH; desf.
      all: try (rewrite SAMELBL_2_0 in HH; [|done]).
      all: try (rewrite SAMELBL_2_0 in HH; [|done]).
      all: try (rewrite SAMELBL_3_0 in HH; [|done]).
      all: try (rewrite SAMELBL_3_0 in HH; [|done]).
      all: splits; auto. }
    unfolder; intros x y HH; desf.
    all: try (rewrite SAMELBL_2_0; [|done]).
    all: try (rewrite SAMELBL_2_0; [|done]).
    all: try (rewrite SAMELBL_3_0; [|done]).
    all: try (rewrite SAMELBL_3_0; [|done]).
    all: splits; auto. }

  assert (forall r r',
             restr_rel (events_set P2 ∪₁ events_set P3) r ∩
                       ((fun e => ifP lset (events P2) e then λ P2 e else λ P3 e) ⋄ r') ≡
             restr_rel (events_set P2 ∪₁ events_set P3) (r ∩ (λ P0 ⋄ r'))) as P23λmapAlt.
  { ins. rewrite <- inter_restr_absorb_r. unfold P23lambda in *.
    rewrite P23λmap. basic_solver 10. }
  assert (restr_rel (events_set P3) (dep P0) ≡ dep P3)
    as DEP_0_3.
  { now erewrite <- dep_restr2 with (P2 := P3); [|apply PE]. }

  assert (restr_rel (events_set P2) (dep P0) ≡ dep P2)
    as DEP_0_2.
  { erewrite <- dep_restr2 with (P2 := P2); [|now apply PE0].
    erewrite <- dep_restr1 with (P1 := P12); [|now apply PE].
    rewrite restr_restr, EVENTS12.
    basic_solver 10. }

  assert (restr_rel (events_set P1) (dep P0) ≡ dep P1)
    as DEP_0_1.
  { erewrite <- dep_restr1 with (P1 := P1); [|now apply PE0].
    erewrite <- dep_restr1 with (P1 := P12); [|now apply PE].
    rewrite restr_restr, EVENTS12.
    basic_solver 10. }

  assert (wf P13) as WF13.
  { edestruct SeqBuilder.partial_wf with (P1:=P1) (P2:=P3) (P12:=P13) as [AA BB];
      eauto; try easy.
    subst P13 P13dep. unfold SeqBuilder.t in *; ins.
    unfold P13lambda in *.
    constructor; try apply BB; try apply AA; clear AA BB.
    all: try now constructor;
      [ apply irreflexive_restr, WF | apply transitive_restr, WF].
    all: unfold events_set; ins. 
    all: ins; rewrite ?lset_app, ?restr_rel2E; auto.
    { eapply functional_mori; [|by apply WF].
      rewrite RMW0. red. basic_solver. }
    { rewrite RMW13REST.
      etransitivity.
      2: by apply inclusion_restr with (dom:=events_set P1 ∪₁ events_set P3).
      rewrite P13λmap.
      apply restr_rel_mori; [easy|apply WF]. }
    { rewrite (wf_rmw_dep WF1), (wf_rmw_dep WF3).
      rewrite <- DEP_0_1, <- DEP_0_3.
      basic_solver. }
    { rewrite RMW13REST, <- restr_transp, seq_restr, P13λmapAlt.
      now rewrite <- restr_rel_cr; apply restr_rel_mori; [|apply WF]. }
    rewrite <- inter_restr_absorb_l, P13λmap, <- restr_inter.
    rewrite RMW13REST, <- restr_transp, seq_restr.
    now rewrite <- restr_rel_cr; apply restr_rel_mori; [|apply WF]. }
  assert (wf P23) as WF23.
  { edestruct SeqBuilder.partial_wf with (P1:=P2) (P2:=P3) (P12:=P23) as [AA BB];
      eauto; try easy.
    subst P23 P23dep. unfold SeqBuilder.t in *; ins.
    unfold P23lambda in *.
    constructor; try apply BB; try apply AA; clear AA BB.
    all: try now constructor;
      [ apply irreflexive_restr, WF | apply transitive_restr, WF].
    all: unfold events_set; ins. 
    all: ins; rewrite ?lset_app, ?restr_rel2E; auto.
    { eapply functional_mori; [|by apply WF].
      rewrite RMW0. red. basic_solver. }
    { rewrite RMW23REST.
      etransitivity.
      2: by apply inclusion_restr with (dom:=events_set P2 ∪₁ events_set P3).
      rewrite P23λmap.
      apply restr_rel_mori; [easy|apply WF]. }
    { rewrite (wf_rmw_dep WF2), (wf_rmw_dep WF3).
      rewrite <- DEP_0_2, <- DEP_0_3.
      basic_solver. }
    { rewrite RMW23REST, <- restr_transp, seq_restr, P23λmapAlt.
      now rewrite <- restr_rel_cr; apply restr_rel_mori; [|apply WF]. }
    rewrite <- inter_restr_absorb_l, P23λmap, <- restr_inter.
    rewrite RMW23REST, <- restr_transp, seq_restr.
    now rewrite <- restr_rel_cr; apply restr_rel_mori; [|apply WF]. }

  assert (SEQ P13 P1 P3) as SEQ13.
  { subst P13 P13dep. constructor; auto; ins; try easy.
    assert ((events_set P1 ∪₁ events_set P3) ∩₁ events_set P1 ≡₁ events_set P1) as AA1.
    { clear. basic_solver. }
    assert ((events_set P1 ∪₁ events_set P3) ∩₁ events_set P3 ≡₁ events_set P3) as AA2.
    { clear. basic_solver. }
    assert (events_set P12 ∩₁ events_set P1 ≡₁ events_set P1) as AA3.
    { rewrite EVENTS12. clear. basic_solver. }
    assert (pomset_union P0 P12 P3) as BB by apply PE.

    constructor; ins; auto.
    all: rewrite restr_restr, ?AA1, ?AA2; try apply PE.
    all: etransitivity; [|now apply PE0].
    all: rewrite <- ?(dep_restr1    BB), <- ?(sync_restr1 BB),
                 <- ?(perloc_restr1 BB), <- ?(rf_restr1   BB).
    all: now rewrite restr_restr, ?AA3. }

  assert (SEQ P23 P2 P3) as SEQ23.
  { subst P23 P23dep. constructor; auto; ins; try easy.
    assert ((events_set P2 ∪₁ events_set P3) ∩₁ events_set P2 ≡₁ events_set P2) as AA1.
    { clear. basic_solver. }
    assert ((events_set P2 ∪₁ events_set P3) ∩₁ events_set P3 ≡₁ events_set P3) as AA2.
    { clear. basic_solver. }
    assert (events_set P12 ∩₁ events_set P2 ≡₁ events_set P2) as AA3.
    { rewrite EVENTS12. clear. basic_solver. }
    assert (pomset_union P0 P12 P3) as BB by apply PE.

    constructor; ins; auto.
    all: rewrite restr_restr, ?AA1, ?AA2; try apply PE.
    all: etransitivity; [|now apply PE0].
    all: rewrite <- ?(dep_restr1    BB), <- ?(sync_restr1 BB),
                 <- ?(perloc_restr1 BB), <- ?(rf_restr1   BB).
    all: now rewrite restr_restr, ?AA3. }

  assert (forall ψ ϕ ξ ϕ' ξ',
             ((¬ ψ ∧ ϕ) ∨ (ψ ∧ ξ)) ∨ ((¬ ψ ∧ ϕ') ∨ (ψ ∧ ξ')) ⇔
             ((¬ ψ ∧ (ϕ ∨ ϕ')) ∨ (ψ ∧ (ξ ∨ ξ')))) as AAA.
  { split; red_helper; ins; desf. }

  eapply interp_if with (P1:=P13) (P2:=P23); eauto.
  1,2: now eapply interp_seq; eauto.
  constructor; auto.
  4: { ins. now rewrite (seq_pt PE), (if_pt PE0). }
  { subst P13 P13dep P23 P23dep; unfold SeqBuilder.t.
    constructor; unfold events_set; ins.
    all: try rewrite !lset_app; try easy.
    all: try (clear; basic_solver 1).
    { rewrite (events_union (seq_pomset_union PE)), EVENTS12.
      clear. basic_solver. }
    rewrite (rmw_union (seq_pomset_union PE)).
    rewrite (rmw_union (if_pomset_union PE0)).
    clear. basic_solver. }
  { red. ins. unfold SeqBuilder.tlambda; split; intros HH; desf; symmetry; auto.
    { apply EVENTS13 in HH. destruct HH; desf; auto. }
    apply EVENTS23 in HH. destruct HH; desf; auto. }
  2: { rewrite (seq_term PE), (if_pt PE0).
       rewrite !elim_dneg.
       rewrite disj_conj_distrib2.
       rewrite (if_term PE0).
       rewrite !elim_dneg.
       rewrite conj_assoc.
       arewrite ((¬ Formula.eqEE m (Expr.val 0) ∧ term P1 ∨
                  Formula.eqEE m (Expr.val 0) ∧ term P2)
                 ∧ ¬ Formula.eqEE m (Expr.val 0) ⇔
                     ¬ Formula.eqEE m (Expr.val 0) ∧ term P1).
       { split; red_helper; ins; desf. }
       rewrite conj_assoc.
       arewrite ((¬ Formula.eqEE m (Expr.val 0) ∧ term P1 ∨
                  Formula.eqEE m (Expr.val 0) ∧ term P2)
                 ∧ Formula.eqEE m (Expr.val 0) ⇔
                                Formula.eqEE m (Expr.val 0) ∧ term P2).
       { split; red_helper; ins; desf. }
       rewrite <- !conj_assoc.
       subst P13 P23; ins.
       now rewrite TP1, TP2. }
  ins. rewrite (seq_κ PE). subst P13. subst P23. unfold SeqBuilder.t.
  unfold seq_κ_def, if_κ_def.
  unfold events_set in *; ins.
  desf; ins.
  all: rewrite ?(if_κ PE0).
  all: rewrite ?(if_pt PE0).
  all: unfold if_κ_def; desf; unfold events_set in *; ins.

  all: try match goal with
           | H : lset (events ?X) _, A : IFF ?X _ _ _ |- _ => apply A in H; destruct H
           end.
  all: try match goal with
           | H : lset (_ ++ _) _ |- _ => apply lset_app in H; destruct H
           end.
  all: try match goal with
           | H : ~ lset (_ ++ _) _ |- _ =>
             now exfalso; apply H; apply lset_app; red; auto
           end.
  all: try match goal with
           | H : ~ lset (events ?X) _, A : IFF ?X _ _ _ |- _ =>
             now exfalso; apply H; apply A; red; auto
           end.
  all: desf.

  all: try now exfalso; eapply NR1; eauto.
  all: try now exfalso; eapply NR2; eauto.
  all: try now exfalso; eapply NR3; eauto.

  (* Long run... *)
  all: try now match goal with
               | H : lset (_ ++ _) _ |- _ => apply lset_app in H; destruct H
               end; desf.

  all: try rewrite !disj_false_l.
  all: try rewrite !elim_dneg.
  all: try reflexivity.
  all: rewrite ?AAA.
  all: rewrite ?disj_conj_distrib2, ?disjA.
  all: try (apply disj_more; (apply conj_more; [easy|])).
  all: try (apply disj_more; [easy|]).
  all: try (apply disj_more; [|apply disj_more]; (apply conj_more; [easy|])).
  all: try (apply disj_more; (apply conj_more; [easy|])).
  all: try now apply TP3; auto.
  all: try now apply TP4; auto.
  all: try easy.
  
  all: rewrite disj_sym, disjA.
  all: apply disj_more; try apply conj_more;
    try easy; try (apply TP3; auto).
  all: rewrite disj_sym.
  all: apply disj_more; try apply conj_more; try easy;
    try easy; try (apply TP4; auto).
Qed.
