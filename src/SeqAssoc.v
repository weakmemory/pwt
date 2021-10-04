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

Set Implicit Arguments.

Open Scope formula_scope.
Open Scope list_additional_scope.

(* This is an auxiliary lemma, used in seq_assoc.
   While seq_assoc proves equivalence of two sets,
   seq_assoc1 and seq_assoc2 show one-way inclusion.
   This lemma shows that semantics of s1 ; (s2 ; s3) is a
   subset of semantics of (s1 ; s2) ; s3 *)
Lemma seq_assoc2 (α : thread_id) s1 s2 s3 :
  Semantics α (Stmt.seq s1 (Stmt.seq s2 s3)) ⊆₁
  Semantics α (Stmt.seq (Stmt.seq s1 s2) s3).
Proof.
  (* dep P ⊆ dep P1 ∪ dep P2 ∪ (events_set P1 × events_set P2)^⋈ *)
  assert ((forall {P P1 P2} (SEQ12 : SEQ P P1 P2),
              dep P1 ≡ restr_rel (events_set P1) (dep P))
          /\
          (forall {P P1 P2} (SEQ12 : SEQ P P1 P2),
             dep P2 ≡ restr_rel (events_set P2) (dep P)))
         as [DEP_UB1 DEP_UB2].
  { split; ins.
    erewrite dep_restr1; [done | by apply SEQ12].
    erewrite dep_restr2; [done | by apply SEQ12]. }
  intros P0 PP0.
  assert (wf P0) as WF by eby eapply semantics_wf.
  inv PP0.
  rename s0 into s1, P2 into P23.
  inv interp2.
  rename s0 into s2, s4 into s3.

  assert (events_set P23 ≡₁ events_set P2 ∪₁ events_set P3) as EVENTS23
      by apply PE0.
  assert (wf P1 /\ wf P2 /\ wf P3) as [WF1 [WF2 WF3]].
  { splits; eapply semantics_wf; eauto. }

  assert (forall d (DD : events_set P23 d),
             λ P23 d = λ P0 d) as SAMELBL_23_0.
  { symmetry. apply (seq_label_union PE); auto. }

  assert (forall d (DD : events_set P2 d),
             λ P23 d = λ P2 d) as SAMELBL_23_2.
  { apply (seq_label_union PE0); auto. }

  assert (forall d (DD : events_set P2 d),
             λ P2 d = λ P0 d) as SAMELBL_2_0.
  { ins. etransitivity; [| apply SAMELBL_23_0, EVENTS23; basic_solver].
    symmetry. apply (seq_label_union PE0); auto. }

  assert (forall d (DD : events_set P3 d),
             λ P3 d = λ P0 d) as SAMELBL_3_0.
  { ins. etransitivity; [| apply SAMELBL_23_0, EVENTS23; basic_solver].
    symmetry. apply (seq_label_union PE0); auto. }

  assert (forall d (DD : events_set P1 d),
             λ P1 d = λ P0 d) as SAMELBL_1_0.
  { ins. symmetry. apply (seq_label_union PE); auto. }

  assert (forall d (DD : events_set P3 d),
             λ P23 d = λ P3 d) as SAMELBL_23_3.
  { apply (seq_label_union PE0); auto. }
  set (P12lambda := fun e =>
                      ifP (events_set P1 e)
                      then (λ P1 e)
                      else (λ P2 e)).
  set (P12dep := restr_rel (events_set P1 ∪₁ events_set P2) (dep P0)).
  eset (P12 :=
          {|
           events := events P1 ++ events P2;
           dep    := P12dep;
           sync   := restr_rel (events_set P1 ∪₁ events_set P2) (sync P0);
           perloc := restr_rel (events_set P1 ∪₁ events_set P2) (perloc P0);
           λ      := P12lambda;
           κ      := seq_κ_def P1 P2 P12lambda P12dep;
           τ D ψ  := τ P1 D (τ P2 D ψ);
           rmw    := rmw P1 ∪ rmw P2;
           term   := term P1 ∧ (τ P1 (events_set P1) (term P2));
           rf     := restr_rel (events_set P1 ∪₁ events_set P2) (rf P0);
          |}
       ).
  subst P12dep P12lambda.

  assert (events_set P12 ≡₁ events_set P1 ∪₁ events_set P2) as EVENTS12.
  { unfold events_set.
    by rewrite <- lset_app. }

  assert (forall d (DD : events_set P12 d),
             λ P12 d = λ P0 d) as SAMELBL_12_0.
  { ins; desf; [by apply SAMELBL_1_0 |].
    apply SAMELBL_2_0.
    apply EVENTS12 in DD.
    destruct DD; desf. }

  assert (forall ψ,
             τ P23 (events_set P23) ψ ⇔
             τ P2 (events_set P2) (τ P3 (events_set P3) ψ)) as TAUP23.
  { ins. erewrite (seq_pt PE0).
    erewrite (pt_more (τ P2 (events_set P23))).
    2: by apply WF2.
    all: erewrite wf_pt_family_equiv_on_E; [easy| |]; auto.
    all: rewrite EVENTS23; basic_solver. }

  assert (restr_rel (events_set P2) (dep P0) ≡ dep P2)
    as DEP_0_2.
  { rewrite
      (DEP_UB1 P23 P2 P3 PE0),
    (DEP_UB2 P0 P1 P23 PE),
    restr_restr,
    EVENTS23.
    basic_solver 10. }

  assert (restr_rel (events_set P3) (dep P0) ≡ dep P3)
    as DEP_0_3.
  { rewrite
      (DEP_UB2 P23 P2 P3 PE0),
    (DEP_UB2 P0 P1 P23 PE),
    restr_restr,
    EVENTS23.
    basic_solver 10. }

  assert (restr_rel (events_set P1) (dep P0) ≡ dep P1)
    as DEP_0_1.
  { rewrite (DEP_UB1 P0 P1 P23 PE); auto. }

  assert (restr_rel (events_set P23) (dep P0) ≡ dep P23)
    as DEP_0_23.
  { rewrite (DEP_UB2 P0 P1 P23 PE); auto. }

  assert (restr_rel (events_set P12) (dep P0) ≡ dep P12)
    as DEP_0_12.
  { by rewrite EVENTS12. }

  assert (restr_rel (events_set P2) (dep P23) ≡ dep P2)
    as DEP_23_2.
  { rewrite (DEP_UB1 P23 P2 P3 PE0); auto. }

  assert (restr_rel (events_set P3) (sync P0) ≡ sync P3)
    as SYNC_0_3.
  { erewrite <- sync_restr2 with (P2 := P3); [| by apply PE0].
    erewrite <- sync_restr2 with (P2 := P23); [| by apply PE].
    rewrite restr_restr, EVENTS23.
    basic_solver 10. }

  assert (restr_rel (events_set P2) (sync P0) ≡ sync P2)
    as SYNC_0_2.
  { erewrite <- sync_restr1 with (P1 := P2); [| by apply PE0].
    erewrite <- sync_restr2 with (P2 := P23); [| by apply PE].
    rewrite restr_restr, EVENTS23.
    basic_solver 10. }

  assert (restr_rel (events_set P1) (sync P0) ≡ sync P1)
    as SYNC_0_1.
  { erewrite sync_restr1 with (P2 := P23); auto. apply PE. }

  assert (restr_rel (events_set P3) (perloc P0) ≡ perloc P3)
    as PERLOC_0_3.
  { erewrite <- perloc_restr2 with (P2 := P3); [| by apply PE0].
    erewrite <- perloc_restr2 with (P2 := P23); [| by apply PE].
    rewrite restr_restr, EVENTS23.
    basic_solver 10. }

  assert (restr_rel (events_set P1) (perloc P0) ≡ perloc P1)
    as PERLOC_0_1.
  { erewrite perloc_restr1 with (P2 := P23); auto. apply PE. }

  assert (restr_rel (events_set P3) (rf P0) ≡ rf P3)
    as RF_0_3.
  { erewrite <- rf_restr2 with (P2 := P3); [| by apply PE0].
    erewrite <- rf_restr2 with (P2 := P23); [| by apply PE].
    rewrite restr_restr, EVENTS23.
    basic_solver 10. }

  assert (restr_rel (events_set P1) (rf P0) ≡ rf P1)
    as RF_0_1.
  { erewrite rf_restr1 with (P2 := P23); auto. apply PE. }

  assert (restr_rel (events_set P2) (perloc P0) ≡ perloc P2)
    as PERLOC_0_2.
  { erewrite <- perloc_restr1 with (P1 := P2); [| by apply PE0].
    erewrite <- perloc_restr2 with (P2 := P23); [| by apply PE].
    rewrite restr_restr, EVENTS23.
    basic_solver 10. }

  assert (restr_rel (events_set P2) (rf P0) ≡ rf P2)
    as RF_0_2.
  { erewrite <- rf_restr1 with (P1 := P2); [| by apply PE0].
    erewrite <- rf_restr2 with (P2 := P23); [| by apply PE].
    rewrite restr_restr, EVENTS23.
    basic_solver 10. }

  assert (rmw P0 ≡ rmw P1 ∪ (rmw P2 ∪ rmw P3)) as RMW0.
  { rewrite rmw_union with (P:=P0 ); [|by apply PE].
    now rewrite rmw_union with (P:=P23); [|by apply PE0]. }

  assert (forall φ, τ P2 (events_set P23) (τ P3 (events_set P23) φ)
                  ⇔ τ P2 (events_set P2) (τ P3 (events_set P3) φ))
  as PT_COMP23.
  { ins.
    transitivity (τ P2 (events_set P2) (τ P3 (events_set P23) φ)).
    { apply  wf_pt_family_equiv_on_E; auto.
      rewrite EVENTS23; basic_solver. }
    apply pt_more; [by apply WF2|].
    apply  wf_pt_family_equiv_on_E; eauto.
    rewrite EVENTS23; basic_solver. }

  assert (rmw P1 ∪ rmw P2 ⊆ restr_rel (events_set P1 ∪₁ events_set P2) (rmw P0))
    as RMW12REST.
  { rewrite (wf_rmwE_ WF1), (wf_rmwE_ WF2).
    arewrite (rmw P1 ⊆ rmw P0) by (rewrite RMW0; eauto with hahn).
    arewrite (rmw P2 ⊆ rmw P0) by (rewrite RMW0; eauto with hahn).
    basic_solver. }

  assert (forall r,
             restr_rel (events_set P1 ∪₁ events_set P2)
                       ((fun e => ifP lset (events P1) e then λ P1 e else λ P2 e) ⋄ r) ≡
             restr_rel (events_set P1 ∪₁ events_set P2)
                       (λ P0 ⋄ r)) as P12λmap.
  { unfold events_set.
    ins; split.
    { unfolder; intros x y HH; desf.
      all: try (rewrite SAMELBL_1_0 in HH; [|done]).
      all: try (rewrite SAMELBL_1_0 in HH; [|done]).
      all: try (rewrite SAMELBL_2_0 in HH; [|done]).
      all: try (rewrite SAMELBL_2_0 in HH; [|done]).
      all: splits; auto. }
    unfolder; intros x y HH; desf.
    all: try (rewrite SAMELBL_1_0; [|done]).
    all: try (rewrite SAMELBL_1_0; [|done]).
    all: try (rewrite SAMELBL_2_0; [|done]).
    all: try (rewrite SAMELBL_2_0; [|done]).
    all: splits; auto. }

  assert (forall r r',
             restr_rel (events_set P1 ∪₁ events_set P2) r ∩
                       ((fun e => ifP lset (events P1) e then λ P1 e else λ P2 e) ⋄ r') ≡
             restr_rel (events_set P1 ∪₁ events_set P2) (r ∩ (λ P0 ⋄ r'))) as P12λmapAlt.
  { ins. rewrite <- inter_restr_absorb_r.
    rewrite P12λmap. basic_solver 10. }
  
  assert (forall d (PD1 : events_set P1 d) (PD2 : events_set P2 d),
             λ P1 d = λ P2 d) as EQLAB.
  { ins.
    rewrite SAMELBL_1_0; auto.
    now rewrite SAMELBL_2_0. }

  assert (wf P12) as WF12.
  { edestruct SeqBuilder.partial_wf with (P1:=P1) (P2:=P2) as [AA BB]; eauto.
    subst P12.
    constructor; try apply BB; try apply AA; clear AA BB.
    all: try now constructor;
      [ apply irreflexive_restr, WF | apply transitive_restr, WF].
    all: unfold events_set; ins. 
    all: ins; rewrite ?lset_app, ?restr_rel2E; auto.
    { rewrite <- inter_restr_absorb_l.
      rewrite P12λmap. rewrite <- restr_inter.
      apply restr_rel_mori; [easy|apply WF]. }
    { eapply functional_mori; [|by apply WF].
      rewrite RMW0. red. basic_solver. }
    { rewrite RMW12REST.
      etransitivity.
      2: by apply inclusion_restr with (dom:=events_set P1 ∪₁ events_set P2).
      rewrite P12λmap.
      apply restr_rel_mori; [easy|apply WF]. }
    { rewrite (wf_rmw_sync WF1), (wf_rmw_sync WF2).
      rewrite <- SYNC_0_1, <- SYNC_0_2.
      basic_solver. }
    { rewrite (wf_rmw_perloc WF1), (wf_rmw_perloc WF2).
      rewrite <- PERLOC_0_1, <- PERLOC_0_2.
      basic_solver. }

    1-3: rewrite RMW12REST, <- restr_transp, seq_restr, P12λmapAlt.
    1-3: by rewrite <- restr_rel_cr; apply restr_rel_mori; [easy|apply WF].

    all: rewrite <- inter_restr_absorb_l, P12λmap, <- restr_inter.
    all: rewrite RMW12REST, <- restr_transp, seq_restr.
    all: by rewrite <- restr_rel_cr; apply restr_rel_mori; [easy|apply WF]. }

  (* Semantics α (Stmt.seq s1 (Stmt.seq s2 s3)) P0 *)
  (*  Semantics α (Stmt.seq (Stmt.seq s1 s2) s3) P0 *)
  eapply interp_seq with (P1 := P12) (P2 := P3); eauto.
  { (* Semantics α (Stmt.seq s1 s2) P12 *)
    eapply interp_seq; eauto.
    constructor; ins; try easy.
    { (* pomset_union P12 P1 P2 *)
      constructor; ins.

      (* dep2 ∪ dep3 ⊆ restr_rel (E2 ∪₁ E3) dep0 *)
      1,2: now rewrite restr_restr, set_inter_absorb_l; auto with hahn.
      all: now rewrite restr_restr, set_inter_absorb_l; auto with hahn. }

    { (* label_union P12 P1 P2 *)
      constructor; ins.
      { basic_solver. }
      desf; auto. }
    { assert ((sync P0)^? d e) as SYNC_DE.
      { apply (seq_sync_delay PE); auto; [| by rewrite SAMELBL_23_2].
        apply EVENTS23; basic_solver. }
      destruct SYNC_DE; basic_solver 10. }
    assert ((perloc P0)^? d e) as PERLOC_DE.
    { apply (seq_coh_delay PE); auto; [| by rewrite SAMELBL_23_2].
      apply EVENTS23; basic_solver. }
    destruct PERLOC_DE; basic_solver 10. }

  (* SEQ P0 P12 P3 *)
  constructor; auto.
  { (* pomset_union P0 P12 P3 *)
    constructor; ins.
    all: inv PE; inv PE0.
    { (* events_set P0 ≡₁ events_set P12 ∪₁ events_set P3 *)
      erewrite events_union with (P:=P0) (P2:=P23); eauto.
      rewrite EVENTS23, EVENTS12. basic_solver. }
    all: try now rewrite EVENTS12.
    (* rmw P0 ≡ rmw P1 ∪ rmw P2 ∪ rmw P3 *)
    rewrite RMW0, unionA; done. }

  { (* label_union P0 P12 P3 *)
    constructor.
    2: { intros eP3.
         transitivity (λ P23 e).
         2: by eapply (seq_label_union PE0).
         eapply (seq_label_union PE).
         eapply seq_pomset_union; eauto.
         basic_solver. }
    intros eP12.
    unfold events_set in *; simpls.
    apply in_app_or in eP12.
    destruct eP12.
    all: desf; auto; try by (symmetry; apply SAMELBL_1_0; auto).
    rewrite SAMELBL_2_0; auto. }
  { ins.
    etransitivity.
    { eapply seq_κ; eauto. }
    unfold seq_κ_def. desf.
    all: unfold events_set; ins.
    all: try by (exfalso;
      match goal with
      | H : ~ events_set ?X _,
        A : events_set ?X ≡₁ _ ∪₁ _ 
        |- _ => apply H; apply A; basic_solver
      end).
    all: try by (exfalso;
                 match goal with
                 | B : events_set ?X _,
                   A : events_set ?X ≡₁ _ ∪₁ _ 
                   |- _ => apply A in B; destruct B
                 end; desf;
                 match goal with
                 | H : ~ events_set ?X _,
                   A : events_set ?X ≡₁ _ ∪₁ _ 
                   |- _ => apply H; apply A
                 end; basic_solver).
    all: try rewrite !disj_false_l.
    all: try subst P12.
    all: ins; unfold seq_κ_def.
    all: desf.
    all: try rewrite !disj_false_l.
    all: try easy.
    all: try by (exfalso;
                 match goal with
                 | H : ~ is_r' _ |- _ =>
                     by apply H; rewrite ?SAMELBL_23_0,
                                 ?SAMELBL_1_0, ?SAMELBL_3_0,
                                 ?SAMELBL_2_0, ?SAMELBL_12_0 in *;
                   auto
                 | H : events_set _ _ |- _ =>
                   by apply EVENTS23 in H; destruct H; eauto
                 | H : events_set _ _ |- _ =>
                   by apply EVENTS12 in H; destruct H; eauto
                 | H : ~ (events_set _ _) |- _ =>
                   by apply H; red; ins; apply lset_app; basic_solver
                 | H : ~ (events_set _ _) |- _ =>
                   by apply H; apply EVENTS23; basic_solver
                 end).
    all: try rewrite !disjA.
    all: try (apply disj_more; [easy|]).
    (* { rewrite pt_preserves_disj; [| by apply WF1]. *)
    (*   apply disj_more. *)
    all: erewrite pt_more; [| apply WF1  | by apply seq_κ; eauto].
    all: unfold seq_κ_def; desf.
    all: try by (exfalso;
                 match goal with
                 | H : ~ is_r' _ |- _ =>
                   by apply H; rewrite ?SAMELBL_23_0, ?SAMELBL_1_0,
                            ?SAMELBL_3_0 in *; auto
                 | H : ~ (events_set _ _) |- _ =>
                   by apply H; red; ins; apply lset_app; basic_solver
                 end).
    all: try (rewrite pt_more; [| by apply WF1 | by apply disj_false_l]).
    all: try (rewrite pt_preserves_disj; [| by apply WF1]).
    all: try match goal with
             | [ |- context[τ _ (lset (?X ++ ?Y)) ?phi] ] =>
               rewrite !wf_pt_family_equiv_on_E with
                   (C := lset (X ++ Y))
                   (D := lset (events P1));
                 [| by apply WF1 | rewrite lset_app; basic_solver]
             end.
    all: try (match goal with
              | [ |- context[τ _ _ (τ _ (lset (?X ++ ?Y)) ?phi)]]
                =>
                rewrite pt_more with
                    (x := (τ P2 (lset (X ++ Y)) phi));
                [| by apply WF1 |
                 apply wf_pt_family_equiv_on_E with
                     (D := lset (events P2));
                 [by apply WF2 | rewrite lset_app; basic_solver]]
              end).
    all: try apply disj_more.
    all: try easy.
    all: try (apply pt_more; [by apply WF1 |]).
    all: try (apply wf_pt_family_equiv_on_E;
              [by (try apply WF1; try apply WF2)|]).

    all: try (rewrite !prefix_inter_restr;
              [| basic_solver 20 | basic_solver 30]).
    1,4,5,8: basic_solver 20.
    1,3: by rewrite DEP_23_2, DEP_0_2.
    all: transitivity (prefix (restr_rel (events_set P23) (dep P0))
                             (eq e) ∩₁ events_set P2);
      [by rewrite DEP_0_23 | rewrite EVENTS23; basic_solver 10]. }
  { (* tau *)
    ins.
    erewrite seq_pt; eauto.
    apply pt_more; [by apply WF1| by apply seq_pt]. }
  { (* term *)
    etransitivity; [by eapply seq_term; eauto|].
    subst P12; unfold events_set; ins.
    rewrite pt_more with (x := term P23);
      [| by apply WF1 | by apply (seq_term PE0)].
    rewrite pt_preserves_conj, conjA; [| by apply WF1].
    do 2 (apply conj_more; [easy|]).
    rewrite wf_pt_family_equiv_on_E; [apply pt_more | |].
    1,3: by apply WF1.
    1: apply wf_pt_family_equiv_on_E; [by apply WF2 |].
    all: by rewrite lset_app; basic_solver. }
  { (* sync_delays *)
    ins. desf.
    { eapply (seq_sync_delay); eauto.
      { apply EVENTS23. basic_solver. }
      erewrite SAMELBL_23_3; eauto. }
    apply EVENTS12 in E1D.
    red in E1D; desf.
    assert ((sync P23)^? d e) as AA.
    { eapply (seq_sync_delay); eauto. }
    enough ((sync P23)^? ⊆ (sync P0)^?) as BB.
    { apply BB; auto. }
    apply clos_refl_mori.
    rewrite <- sync_union with (P:=P0); [|by apply PE].
    eauto with hahn. }

  (* coh_delays *)
  ins. desf.
  { eapply (seq_coh_delay); eauto.
    { apply EVENTS23. basic_solver. }
    erewrite SAMELBL_23_3; eauto. }
  apply EVENTS12 in E1D.
  red in E1D; desf.
  assert ((perloc P23)^? d e) as AA.
  { eapply (seq_coh_delay); eauto. }
  enough ((perloc P23)^? ⊆ (perloc P0)^?) as BB.
  { apply BB; auto. }
  apply clos_refl_mori.
  rewrite <- perloc_union with (P:=P0); [|by apply PE].
  eauto with hahn.
Qed.


(* This is an auxiliary lemma, used in seq_assoc.
   While seq_assoc proves equivalence of two sets,
   seq_assoc1 and seq_assoc2 show one-way inclusion.
   This lemma shows that semantics of (s1 ; s2) ; s3 is a
   subset of semantics of s1 ; (s2 ; s3) *)
Lemma seq_assoc1 (α : thread_id) s1 s2 s3 :
  Semantics α (Stmt.seq (Stmt.seq s1 s2) s3) ⊆₁
  Semantics α (Stmt.seq s1 (Stmt.seq s2 s3)).
Proof.
  (* dep P ⊆ dep P1 ∪ dep P2 ∪ (events_set P1 × events_set P2)^⋈ *)
  assert ((forall {P P1 P2} (SEQ12 : SEQ P P1 P2),
              dep P1 ≡ restr_rel (events_set P1) (dep P))
          /\
          (forall {P P1 P2} (SEQ12 : SEQ P P1 P2),
             dep P2 ≡ restr_rel (events_set P2) (dep P)))
         as [DEP_UB1 DEP_UB2].
  { split; ins.
    erewrite dep_restr1; [done | by apply SEQ12].
    erewrite dep_restr2; [done | by apply SEQ12]. }
  intros P0 PP0.
  assert (wf P0) as WF by eby eapply semantics_wf.
  inv PP0.
  rename s4 into s3, P1 into P12, P2 into P3.
  inv interp1.
  rename s0 into s1, s4 into s2.

  assert (events_set P12 ≡₁ events_set P1 ∪₁ events_set P2) as EVENTS12
      by apply PE0.
  assert (wf P1 /\ wf P2 /\ wf P3) as [WF1 [WF2 WF3]].
  { splits; eapply semantics_wf; eauto. }


  assert (forall d (DD : events_set P12 d),
             λ P12 d = λ P0 d) as SAMELBL_12_0.
  { symmetry. apply (seq_label_union PE); auto. }

  assert (forall d (DD : events_set P1 d),
             λ P12 d = λ P1 d) as SAMELBL_12_1.
  { apply (seq_label_union PE0); auto. }

  assert (forall d (DD : events_set P1 d),
             λ P1 d = λ P0 d) as SAMELBL_1_0.
  { ins. etransitivity; [| apply SAMELBL_12_0, EVENTS12; basic_solver].
    symmetry. apply (seq_label_union PE0); auto. }

  assert (forall d (DD : events_set P2 d),
             λ P2 d = λ P0 d) as SAMELBL_2_0.
  { ins. etransitivity; [| apply SAMELBL_12_0, EVENTS12; basic_solver].
    symmetry. apply (seq_label_union PE0); auto. }

  assert (forall d (DD : events_set P3 d),
             λ P3 d = λ P0 d) as SAMELBL_3_0.
  { ins. symmetry. apply (seq_label_union PE); auto. }

  (* TODO: make a lemma? *)
  assert (forall d (DD : events_set P2 d),
             λ P12 d = λ P2 d) as SAMELBL_12_2.
  { apply (seq_label_union PE0); auto. }
  set (P23lambda := fun e =>
                      ifP (events_set P2 e)
                      then (λ P2 e)
                      else (λ P3 e)).
  set (P23dep := restr_rel (events_set P2 ∪₁ events_set P3) (dep P0)).
  eset (P23 :=
          {|
           events := events P2 ++ events P3;
           dep    := P23dep;
           sync   := restr_rel (events_set P2 ∪₁ events_set P3) (sync P0);
           perloc := restr_rel (events_set P2 ∪₁ events_set P3) (perloc P0);
           λ      := P23lambda;
           κ      := seq_κ_def P2 P3 P23lambda P23dep;
           τ D ψ  := τ P2 D (τ P3 D ψ);
           rmw    := rmw P2 ∪ rmw P3;
           term   := term P2 ∧ (τ P2 (events_set P2) (term P3));
           rf     := restr_rel (events_set P2 ∪₁ events_set P3) (rf P0);
          |}
       ).
  subst P23dep P23lambda.

  assert (events_set P23 ≡₁ events_set P2 ∪₁ events_set P3) as EVENTS23.
  { unfold events_set.
    by rewrite <- lset_app. }

  assert (forall d (DD : events_set P23 d),
             λ P23 d = λ P0 d) as SAMELBL_23_0.
  { ins; desf; [by apply SAMELBL_2_0 |].
    apply SAMELBL_3_0.
    apply EVENTS23 in DD.
    destruct DD; desf. }

  assert (forall ψ,
             τ P12 (events_set P12) ψ ⇔
             τ P1 (events_set P1) (τ P2 (events_set P2) ψ)) as TAUP12.
  { ins. erewrite (seq_pt PE0).
    erewrite (pt_more (τ P1 (events_set P12))).
    2: by apply WF1.
    all: erewrite wf_pt_family_equiv_on_E; [easy| |]; auto.
    all: rewrite EVENTS12; basic_solver. }

  assert (restr_rel (events_set P1) (dep P0) ≡ dep P1)
    as DEP_0_1.
  { rewrite
      (DEP_UB1 P12 P1 P2 PE0),
    (DEP_UB1 P0 P12 P3 PE),
    restr_restr,
    EVENTS12.
    basic_solver 10. }

  assert (restr_rel (events_set P2) (dep P0) ≡ dep P2)
    as DEP_0_2.
  { rewrite
      (DEP_UB2 P12 P1 P2 PE0),
    (DEP_UB1 P0 P12 P3 PE),
    restr_restr,
    EVENTS12.
    basic_solver 10. }

  assert (restr_rel (events_set P3) (dep P0) ≡ dep P3)
    as DEP_0_3.
  { rewrite (DEP_UB2 P0 P12 P3 PE); auto. }

  assert (restr_rel (events_set P12) (dep P0) ≡ dep P12)
    as DEP_0_12.
  { rewrite (DEP_UB1 P0 P12 P3 PE); auto. }

  assert (restr_rel (events_set P23) (dep P0) ≡ dep P23)
    as DEP_0_23.
  { by rewrite EVENTS23. }

  assert (restr_rel (events_set P1) (dep P12) ≡ dep P1)
    as DEP_12_1.
  { rewrite (DEP_UB1 P12 P1 P2 PE0); auto. }

  assert (restr_rel (events_set P2) (sync P0) ≡ sync P2)
    as SYNC_0_2.
  { erewrite <- sync_restr2 with (P2 := P2); [| by apply PE0].
    erewrite <- sync_restr1 with (P1 := P12); [| by apply PE].
    rewrite restr_restr, EVENTS12.
    basic_solver 10. }

  assert (restr_rel (events_set P3) (sync P0) ≡ sync P3)
    as SYNC_0_3.
  { erewrite sync_restr2 with (P1 := P12); auto. apply PE. }

  assert (restr_rel (events_set P2) (perloc P0) ≡ perloc P2)
    as PERLOC_0_2.
  { erewrite <- perloc_restr2 with (P2 := P2); [| by apply PE0].
    erewrite <- perloc_restr1 with (P1 := P12); [| by apply PE].
    rewrite restr_restr, EVENTS12.
    basic_solver 10. }

  assert (restr_rel (events_set P3) (perloc P0) ≡ perloc P3)
    as PERLOC_0_3.
  { erewrite perloc_restr2 with (P1 := P12); auto. apply PE. }

  assert (restr_rel (events_set P2) (rf P0) ≡ rf P2)
    as RF_0_2.
  { erewrite <- rf_restr2 with (P2 := P2); [| by apply PE0].
    erewrite <- rf_restr1 with (P1 := P12); [| by apply PE].
    rewrite restr_restr, EVENTS12.
    basic_solver 10. }

  assert (restr_rel (events_set P1) (sync P0) ≡ sync P1)
    as SYNC_0_1.
  { erewrite <- sync_restr1 with (P1 := P1); [| by apply PE0].
    erewrite <- sync_restr1 with (P1 := P12); [| by apply PE].
    rewrite restr_restr, EVENTS12.
    basic_solver 10. }

  assert (restr_rel (events_set P1) (perloc P0) ≡ perloc P1)
    as PERLOC_0_1.
  { erewrite <- perloc_restr1 with (P1 := P1); [| by apply PE0].
    erewrite <- perloc_restr1 with (P1 := P12); [| by apply PE].
    rewrite restr_restr, EVENTS12.
    basic_solver 10. }

  assert (restr_rel (events_set P1) (rf P0) ≡ rf P1)
    as RF_0_1.
  { erewrite <- rf_restr1 with (P1 := P1); [| by apply PE0].
    erewrite <- rf_restr1 with (P1 := P12); [| by apply PE].
    rewrite restr_restr, EVENTS12.
    basic_solver 10. }
  
  assert (rmw P0 ≡ rmw P1 ∪ rmw P2 ∪ rmw P3) as RMW0.
  { rewrite rmw_union with (P:=P0 ); [|by apply PE].
    now rewrite rmw_union with (P:=P12); [|by apply PE0]. }
  
  assert ( forall φ, τ P1 (events_set P12) (τ P2 (events_set P12) φ)
                  ⇔ τ P1 (events_set P1) (τ P2 (events_set P2) φ))
  as PT_COMP12.
  { ins.
    transitivity (τ P1 (events_set P1) (τ P2 (events_set P12) φ)).
    { apply  wf_pt_family_equiv_on_E; auto.
      rewrite EVENTS12; basic_solver. }
    apply pt_more; [by apply WF1|].
    apply  wf_pt_family_equiv_on_E; eauto.
    rewrite EVENTS12; basic_solver. }

  assert (rmw P2 ∪ rmw P3 ⊆ restr_rel (events_set P2 ∪₁ events_set P3) (rmw P0))
    as RMW23REST.
  { rewrite (wf_rmwE_ WF2), (wf_rmwE_ WF3).
    arewrite (rmw P2 ⊆ rmw P0) by (rewrite RMW0; eauto with hahn).
    arewrite (rmw P3 ⊆ rmw P0) by (rewrite RMW0; eauto with hahn).
    basic_solver. }

  assert (forall r,
             restr_rel (events_set P2 ∪₁ events_set P3)
                       ((fun e => ifP lset (events P2) e then λ P2 e else λ P3 e) ⋄ r) ≡
             restr_rel (events_set P2 ∪₁ events_set P3)
                       (λ P0 ⋄ r)) as P23λmap.
  { unfold events_set.
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
  { ins. rewrite <- inter_restr_absorb_r.
    rewrite P23λmap. basic_solver 10. }

  assert (forall d (PD2 : events_set P2 d) (PD3 : events_set P3 d),
             λ P2 d = λ P3 d) as EQLAB.
  { ins.
    rewrite SAMELBL_2_0; auto.
    now rewrite SAMELBL_3_0. }

  assert (wf P23) as WF23.
  { edestruct SeqBuilder.partial_wf with (P1:=P2) (P2:=P3) as [AA BB]; eauto.
    subst P23.
    constructor; try apply BB; try apply AA; clear AA BB.
    all: try now constructor;
      [ apply irreflexive_restr, WF | apply transitive_restr, WF].
    all: unfold events_set; ins. 
    all: ins; rewrite ?lset_app, ?restr_rel2E; auto.
    { rewrite <- inter_restr_absorb_l.
      rewrite P23λmap. rewrite <- restr_inter.
      apply restr_rel_mori; [easy|apply WF]. }
    { eapply functional_mori; [|by apply WF].
      rewrite RMW0. red. basic_solver. }
    { rewrite RMW23REST.
      etransitivity.
      2: by apply inclusion_restr with (dom:=events_set P2 ∪₁ events_set P3).
      rewrite P23λmap.
      apply restr_rel_mori; [easy|apply WF]. }
    { rewrite (wf_rmw_sync WF2), (wf_rmw_sync WF3).
      rewrite <- SYNC_0_2, <- SYNC_0_3.
      basic_solver. }
    { rewrite (wf_rmw_perloc WF2), (wf_rmw_perloc WF3).
      rewrite <- PERLOC_0_2, <- PERLOC_0_3.
      basic_solver. }

    1-3: rewrite RMW23REST, <- restr_transp, seq_restr, P23λmapAlt.
    1-3: by rewrite <- restr_rel_cr; apply restr_rel_mori; [easy|apply WF].

    all: rewrite <- inter_restr_absorb_l, P23λmap, <- restr_inter.
    all: rewrite RMW23REST, <- restr_transp, seq_restr.
    all: by rewrite <- restr_rel_cr; apply restr_rel_mori; [easy|apply WF]. }

  (* Semantics α (Stmt.seq s1 (Stmt.seq s2 s3)) P0 *)
  eapply interp_seq with (P1 := P1) (P2 := P23); eauto.
  { (* Semantics α (Stmt.seq s2 s3) P23 *)
    eapply interp_seq; eauto.
    constructor; ins; try reflexivity.
    { (* pomset_union P23 P2 P3 *)
      constructor; ins.
      all: try now rewrite restr_restr, set_inter_absorb_l; auto with hahn.
      rewrite restr_restr, set_inter_absorb_l; auto with hahn.
      now erewrite <- rf_restr2 with (P2 := P3); [| by apply PE]. }
    { (* label_union P23 P2 P3*)
      constructor; ins.
      { basic_solver. }
      desf; auto. }
    { assert ((sync P0)^? d e) as SYNC_DE.
      { apply (seq_sync_delay PE); auto; [| by rewrite SAMELBL_12_2].
        apply (seq_pomset_union PE0); basic_solver. }
      destruct SYNC_DE; basic_solver 10. }
    assert ((perloc P0)^? d e) as PERLOC_DE.
    { apply (seq_coh_delay PE); auto; [|by rewrite SAMELBL_12_2].
      apply (seq_pomset_union PE0); basic_solver. }
    destruct PERLOC_DE; basic_solver 10. }

  (* SEQ P0 P1 P23 *)
  constructor; auto.
  { (* pomset_union P0 P1 P23 *)
    constructor; ins.
    all: inv PE; inv PE0.
    { (* events_set P0 ≡₁ events_set P1 ∪₁ events_set P23 *)
      erewrite events_union with (P:=P0) (P1:=P12); eauto.
      rewrite EVENTS12, EVENTS23. basic_solver. }
    all: try now rewrite EVENTS23.
    (* rmw P1 ∪ rmw P23 ≡ rmw P0 *)
    rewrite <- unionA.
    erewrite rmw_union with (P:=P0); eauto.
    erewrite rmw_union with (P:=P12) (P2:=P2); eauto with hahn. }

  { (* label_union P0 P1 P23 *)
    constructor.
    { intros eP1.
      transitivity (λ P12 e).
      2: by eapply (seq_label_union PE0).
      eapply (seq_label_union PE).
      eapply seq_pomset_union; eauto.
      basic_solver. }
    intros eP23.
    unfold events_set in *; simpls.
    apply in_app_or in eP23.
    destruct eP23.
    all: desf; auto; try by (symmetry; apply SAMELBL_2_0; auto).
    apply (seq_label_union PE); auto. }
  { ins.
    etransitivity.
    { eapply seq_κ; eauto. }
    unfold seq_κ_def. desf.
    all: try by (exfalso;
      match goal with
      | H : ~ events_set ?X _,
        A : events_set ?X ≡₁ _ ∪₁ _ 
        |- _ => apply H; apply A; basic_solver
      end).
    all: try by (exfalso;
                 match goal with
                 | B : events_set ?X _,
                   A : events_set ?X ≡₁ _ ∪₁ _ 
                   |- _ => apply A in B; destruct B
                 end; desf;
                 match goal with
                 | H : ~ events_set ?X _,
                   A : events_set ?X ≡₁ _ ∪₁ _ 
                   |- _ => apply H; apply A
                 end; basic_solver).
    all: try rewrite !disj_false_l.
    all: try erewrite !(seq_precondition PE0).
    all: try subst P23.
    all: ins; unfold seq_κ_def.
    all: desf.
    all: try rewrite !disj_false_l.
    all: try reflexivity.
    all: try by (exfalso;
                 match goal with
                 | H : ~ is_r' _ |- _ =>
                   by apply H; rewrite ?SAMELBL_12_0, ?SAMELBL_3_0,
                            ?SAMELBL_2_0 in *; auto
                 | H : events_set _ _ |- _ =>
                   by apply EVENTS12 in H; destruct H; eauto
                 | H : events_set _ _ |- _ =>
                   by apply EVENTS23 in H; destruct H; eauto
                 | H : ~ (events_set _ _) |- _ =>
                   by apply H; red; ins; apply lset_app; basic_solver
                 | H : ~ (events_set _ _) |- _ =>
                   by apply H; apply EVENTS12; basic_solver
                 end).
    all: try rewrite !disjA.
    all: try (apply disj_more; [reflexivity|]).
    all: try by (rewrite TAUP12;
                 try (apply pt_more; [by apply WF1|]);
                 try (rewrite pt_preserves_disj; [| by apply WF1]);
                 try (rewrite disj_false_l); 
                 reflexivity).
    (* { rewrite pt_preserves_disj; [| by apply WF1]. *)
    (*   apply disj_more. *)
    { rewrite pt_preserves_disj; [| by apply WF1].
      rewrite <- disjA.
      apply disj_more.
      { rewrite (seq_κ PE0).
        unfold seq_κ_def. desf; [reflexivity |].
        rewrite SAMELBL_12_0 in n; auto.
        rewrite SAMELBL_2_0 in i0; auto.
        done. }
      erewrite (seq_pt PE0).
      apply PT_COMP12. }
    { apply disj_more.
      { rewrite (seq_κ PE0).
        unfold seq_κ_def. desf.
        reflexivity. }
      etransitivity.
      2: { apply pt_more; [by apply WF1 |].
           symmetry.
           apply  disj_false_l. }
      rewrite (seq_pt PE0).
      apply PT_COMP12. }
    { rewrite pt_preserves_disj; [| by apply WF1].
      apply disj_more.
      { rewrite (seq_κ PE0).
        unfold seq_κ_def. desf.
        { rewrite disj_false_l; reflexivity. }
        rewrite SAMELBL_12_0 in n1; auto.
        rewrite SAMELBL_2_0 in i0; auto.
        done. }
      rewrite (seq_pt PE0).
      apply PT_COMP12. }
    { rewrite pt_preserves_disj; [| by apply WF1].
      rewrite <- disjA.
      apply disj_more.
      { rewrite (seq_κ PE0).
        unfold seq_κ_def. desf.
        { rewrite SAMELBL_12_0 in i; auto.
          rewrite SAMELBL_2_0 in n0; auto.
          done. }
        apply disj_more; [reflexivity |].
        apply wf_pt_family_equiv_on_E; eauto.
        rewrite !prefix_inter_restr.
        2,3: basic_solver.
        rewrite DEP_0_1, DEP_12_1.
        done. }
      rewrite (seq_pt PE0).
      apply pt_more; [apply WF1 |].
      apply wf_pt_family_equiv_on_E; eauto.
      rewrite !prefix_inter_restr; basic_solver 20. }
    { apply disj_more.
      { rewrite (seq_κ PE0).
        unfold seq_κ_def. desf.
        reflexivity. }
      etransitivity.
      2: { apply pt_more; [by apply WF1 |].
           symmetry.
           apply  disj_false_l. }
      rewrite (seq_pt PE0).
      apply pt_more; [apply WF1 |].
      apply wf_pt_family_equiv_on_E; eauto.
      basic_solver 20. }
    { rewrite pt_preserves_disj; [| by apply WF1].
      apply disj_more.
      { rewrite (seq_κ PE0).
        unfold seq_κ_def. desf.
        { rewrite SAMELBL_12_0 in i; auto.
          rewrite SAMELBL_2_0 in n1; auto.
          done. }
        rewrite disj_false_l.
        apply wf_pt_family_equiv_on_E; eauto.
        transitivity (prefix
                        (restr_rel (events_set P12) (dep P0))
                        (eq e) ∩₁ events_set P1).
        { by rewrite DEP_0_12. }
        rewrite EVENTS12.
        basic_solver 10. }
      rewrite (seq_pt PE0).
      apply pt_more; [apply WF1 |].
      apply wf_pt_family_equiv_on_E; eauto.
      basic_solver 20. }
    { etransitivity.
      2: { apply pt_more; [by apply WF1 |].
           symmetry.
           apply  disj_false_l. }
      rewrite (seq_pt PE0).
      apply pt_more; [apply WF1 |].
      apply wf_pt_family_equiv_on_E; eauto.
      basic_solver 20. }
    { rewrite (seq_κ PE0).
      unfold seq_κ_def. desf; [reflexivity |].
      rewrite SAMELBL_12_0 in n1; auto.
      done. }
    { rewrite (seq_κ PE0).
      unfold seq_κ_def. desf.
      { by rewrite SAMELBL_12_0 in i. }
      apply disj_more; [reflexivity |].
      apply wf_pt_family_equiv_on_E; eauto.
      rewrite !prefix_inter_restr.
      2,3: basic_solver.
      rewrite DEP_0_1, DEP_12_1.
      done. }
    { rewrite (seq_κ PE0).
      unfold seq_κ_def; desf; rewrite disj_false_l; [reflexivity |].
      by rewrite SAMELBL_12_0 in n3. }
    { rewrite (seq_κ PE0).
      unfold seq_κ_def; desf; rewrite disj_false_l.
      { by rewrite SAMELBL_12_0 in i. }
      apply wf_pt_family_equiv_on_E; eauto.
      transitivity (prefix
                      (restr_rel (events_set P12) (dep P0))
                      (eq e) ∩₁ events_set P1).
      { by rewrite DEP_0_12. }
      rewrite EVENTS12.
      basic_solver 10. }
    rewrite (seq_κ PE0).
    unfold seq_κ_def; desf; [| | reflexivity].
    all: exfalso; apply n0; unfold events_set; ins; apply lset_app;
      basic_solver. }
  { (* tau *)
    ins.
    etransitivity; [by eapply seq_pt; eauto|].
    etransitivity; [by eapply seq_pt; eauto|].
    reflexivity. }
  { (* term *)
    etransitivity; [by eapply seq_term; eauto|].
    subst P23; ins.
    erewrite (seq_term PE0).
    rewrite !conjA.
    apply conj_more; [reflexivity|].
    rewrite pt_preserves_conj; [| by apply WF1].
    apply conj_more; [reflexivity|].
    apply TAUP12. }
  { (* sync_delays *)
    ins. desf.
    2: { eapply (seq_sync_delay); eauto.
         { apply EVENTS12. basic_solver. }
         { apply EVENTS23 in E2D. destruct E2D; desf. }
         erewrite SAMELBL_12_1; eauto. }
    assert ((sync P12)^? d e) as AA.
    { eapply (seq_sync_delay); eauto. }
    enough ((sync P12)^? ⊆ (sync P0)^?) as BB.
    { apply BB; auto. }
    apply clos_refl_mori.
    rewrite <- sync_union with (P:=P0); [|by apply PE].
    eauto with hahn. }
  (* coh_delays *)
  ins. desf.
  2: { eapply (seq_coh_delay); eauto.
       { apply EVENTS12. basic_solver. }
       { apply EVENTS23 in E2D. destruct E2D; desf. }
       erewrite SAMELBL_12_1; eauto. }
  assert ((perloc P12)^? d e) as AA.
  { eapply (seq_coh_delay); eauto. }
  enough ((perloc P12)^? ⊆ (perloc P0)^?) as BB.
  { apply BB; auto. }
  apply clos_refl_mori.
  rewrite <- perloc_union with (P:=P0); [|by apply PE].
  eauto with hahn.
Qed.


(* This lemma corresponds to Lemma 4.5 (b).
   It shows associativity of sequential composition.
   In other words, it proves that semantics of s1 ; (s2 ; s3) and
   (s1 ; s2) ; s3 are equal as sets of pomsets. *)
Lemma seq_assoc (α : thread_id) s1 s2 s3 :
  Semantics α (Stmt.seq s1 (Stmt.seq s2 s3)) ≡₁
  Semantics α (Stmt.seq (Stmt.seq s1 s2) s3).
Proof using. split; [apply seq_assoc2|apply seq_assoc1]. Qed.
