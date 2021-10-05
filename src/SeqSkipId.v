From hahn Require Import Hahn.
From imm Require Import Events.
From imm Require Import Prog.
From imm Require Import Execution.

Require Import Pomset.
Require Import Action.
Require Import Formula.
Import Formula.Properties.
Require Import PredTransformer.
Require Import AuxDef.
Require Import AuxRel.
Require Import Language.
Require Import Semantics.

Open Scope formula_scope.

Lemma seq_init_pomset_r P0 (WF : wf P0) : SEQ P0 P0 init_pomset.
Proof.
  unfold init_pomset.
  constructor; ins; try reflexivity.
  3: { split.
       2: apply entails_elim_conj_l1; reflexivity.
       apply entails_elim_conj_r; split; try reflexivity.
       apply WF. }
  2: { unfold seq_κ_def; ins; desf; try reflexivity. by apply WF. }
  constructor; ins.
  all: try rewrite union_false_r; try reflexivity.
  all: try by rewrite restr_relE; symmetry; apply WF.
  all: basic_solver.
Qed.

Lemma seq_init_pomset_l P0 (WF : wf P0) : SEQ P0 init_pomset P0.
Proof.
  unfold init_pomset.
  constructor; ins; try reflexivity.
  4: by apply wf_init_pomset.
  3: { split.
       2: apply entails_elim_conj_l2; reflexivity.
       apply entails_elim_conj_r; split; try reflexivity.
       apply entails_true. }
  2: { unfold seq_κ_def; ins; desf; try rewrite disj_false_l; try reflexivity.
         by apply WF. }
  constructor; ins.
  all: try rewrite union_false_l; try reflexivity.
  all: try by rewrite restr_relE; symmetry; apply WF.
  all: basic_solver.
Qed.

Lemma skip_seq_id_right (α : thread_id) s :
  Semantics α (Stmt.seq s Stmt.skip) ≡₁
  Semantics α s.
Proof.
  split.
  2: { (* Semantics α s ⊆ Semantics α (Stmt.seq s Stmt.skip) *)
       intros P0 PP0.
       eapply interp_seq with (P1:=P0) (P2:=init_pomset); eauto.
       { apply interp_skip; auto. apply skip_init_pomset. }
       apply seq_init_pomset_r. eby eapply semantics_wf. }

  (* Semantics α (Stmt.seq s Stmt.skip) ⊆ Semantics α s *)
  intros P0 PP0. inv PP0.
  enough (pomset_equiv P0 P1) as AA.
  { by rewrite AA. }
  inv interp2.
  assert (forall e, ~ events_set P2 e) as HH.
  { ins. intros AA. eapply (skip_events PE0); eauto. }
  assert (events_set P0 ≡₁ events_set P1) as E1.
  { rewrite (events_union (seq_pomset_union PE)).
    rewrite (skip_events PE0). basic_solver. }
  assert (wf P0) as WF0 by apply PE.
  assert (wf P1) as WF1.
  { eby eapply semantics_wf. }
  constructor; auto.
  { red. ins.
    destruct (classic (events_set P1 a)) as [|NIN].
    { by apply (seq_label_union PE). }
    rewrite (wf_ninEλ WF1); auto.
    rewrite (wf_ninEλ WF0); auto.
    intros AA. apply (events_union (seq_pomset_union PE)) in AA.
    destruct AA; desf.
    eapply (skip_events PE0); eauto. }
  { ins. rewrite (seq_κ PE). unfold seq_κ_def.
    desf; pomset_big_simplifier; try reflexivity. 
    all: try by match goal with
                | H : events_set _ _ |- _ => apply HH in H; desf
                end.
    rewrite (wf_ninEκ WF1); auto. reflexivity. }
  { ins. rewrite (seq_pt PE).
    eapply pt_more; [by apply WF1|].
    rewrite skip_pt; auto. reflexivity. }
  { rewrite (seq_term PE).
    split.
    { apply entails_elim_conj_l1; reflexivity. }
    apply entails_elim_conj_r; split; try reflexivity.
    etransitivity; [eby eapply wf_term|].
    apply pt_entails; [by apply WF1|].
    apply PE0. }
  { rewrite <- (dep_restr1 (seq_pomset_union PE)).
    split; [|basic_solver].
    rewrite <- E1.
    rewrite restr_relE. apply (wf_depE WF0). }
  { rewrite <- (rf_restr1 (seq_pomset_union PE)).
    split; [|basic_solver].
    rewrite <- E1.
    rewrite restr_relE. apply (wf_rfE_ WF0). }
  rewrite (rmw_union (seq_pomset_union PE)).
  pomset_big_simplifier. basic_solver.
Qed.

Lemma skip_seq_id_left (α : thread_id) s :
  Semantics α (Stmt.seq Stmt.skip s) ≡₁
  Semantics α s.
Proof.
  split.
  2: { (* Semantics α s ⊆₁ Semantics α (Stmt.seq Stmt.skip s) *)
       intros P0 PP0.
       eapply interp_seq with (P1:=init_pomset) (P2:=P0); eauto.
       { apply interp_skip; auto. apply skip_init_pomset. }
       apply seq_init_pomset_l. eby eapply semantics_wf. }

  (* Semantics α (Stmt.seq Stmt.skip s) ⊆₁ Semantics α s *)
  intros P0 PP0. inv PP0.
  enough (pomset_equiv P0 P2) as AA.
  { by rewrite AA. }
  inv interp1.
  assert (forall e, ~ events_set P1 e) as HH.
  { ins. intros AA. eapply (skip_events PE0); eauto. }
  assert (events_set P0 ≡₁ events_set P2) as E2.
  { rewrite (events_union (seq_pomset_union PE)).
    rewrite (skip_events PE0). basic_solver. }
  assert (wf P0) as WF0 by apply PE.
  assert (wf P2) as WF2.
  { eby eapply semantics_wf. }
  constructor; auto.
  { red. ins.
    destruct (classic (events_set P2 a)) as [|NIN].
    { by apply (seq_label_union PE). }
    rewrite (wf_ninEλ WF2); auto.
    rewrite (wf_ninEλ WF0); auto.
    intros AA. apply (events_union (seq_pomset_union PE)) in AA.
    destruct AA; desf.
    eapply (skip_events PE0); eauto. }
  { ins. rewrite (seq_κ PE). unfold seq_κ_def.
    desf; pomset_big_simplifier; try reflexivity. 
    all: try by match goal with
                | H : events_set _ _ |- _ => apply HH in H; desf
                end.
    all: rewrite ?disj_false_l, ?(skip_pt PE0); try reflexivity.
    symmetry. by apply WF2. }
  { ins. rewrite (seq_pt PE).
    rewrite (skip_pt PE0). reflexivity. }
  { rewrite (seq_term PE).
    rewrite (skip_term PE0), (skip_pt PE0).
    split.
    { apply entails_elim_conj_l2; reflexivity. }
    apply entails_elim_conj_r; split; try reflexivity.
    apply entails_true. }
  { rewrite <- (dep_restr2 (seq_pomset_union PE)).
    split; [|basic_solver].
    rewrite <- E2.
    rewrite restr_relE. apply (wf_depE WF0). }
  { rewrite <- (rf_restr2 (seq_pomset_union PE)).
    split; [|basic_solver].
    rewrite <- E2.
    rewrite restr_relE. apply (wf_rfE_ WF0). }
  rewrite (rmw_union (seq_pomset_union PE)).
  pomset_big_simplifier. basic_solver.
Qed.

Redirect "skip_seq_id_right.axioms" Print Assumptions skip_seq_id_right.
Redirect "skip_seq_id_left.axioms"  Print Assumptions skip_seq_id_left.
