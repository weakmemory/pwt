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

Set Implicit Arguments.

Open Scope formula_scope.
Open Scope list_additional_scope.

Module SeqBuilder.

Section Internal.
  
Context
  (α : thread_id)
  (s1 s2 : Stmt.t)
  (P1 P2 : pomset)
  (tdep trf : relation Events.Event.t)
  (PE1 : Semantics α s1 P1)
  (PE2 : Semantics α s2 P2).

Definition tlambda :=
  fun e =>
    ifP (events_set P1 e)
    then (λ P1 e)
    else (λ P2 e).

Definition t := {|
  events := events P1 ++ events P2;
  dep    := tdep;
  λ      := tlambda;
  κ      := seq_κ_def P1 P2 tlambda tdep;
  τ D ψ  := τ P1 D (τ P2 D ψ);
  term   := term P1 ∧ (τ P1 (events_set P1) (term P2));
  rf     := trf;
          |}.

Let E := events_set t.

Hypothesis EQLAB :
  forall d (PD1 : events_set P1 d) (PD2 : events_set P2 d),
    λ P1 d = λ P2 d.
 
Variable P12 : pomset.
Hypothesis (EQ : P12 = t).

Lemma props :
  << _WF1          : wf P1 >> /\
  << _WF2          : wf P2 >> /\
  << _EUNION       : events_set P12 ≡₁ events_set P1 ∪₁ events_set P2 >> /\
  << _LAB_UNION    : label_union P12 P1 P2 >> /\
  << _SAMELBL_12_1 : forall d (DD : events_set P1 d), tlambda d = λ P1 d >> /\
  << _SAMELBL_12_2 : forall d (DD : events_set P2 d), tlambda d = λ P2 d >> /\
  << _SDP          : forall l l', set_disjoint (lset (map fst (θ (l' -- l) tlambda)))
                                              (lset l) >> /\
  << _TP1       : forall ψ, τ P1 (events_set t) ψ ⇔ τ P1 (events_set P1) ψ >> /\
  << _TP2       : forall ψ, τ P2 (events_set t) ψ ⇔ τ P2 (events_set P2) ψ >>.
Proof using PE1 PE2 EQLAB EQ.
  subst.
  assert (wf P1 /\ wf P2) as [WF1 WF2].
  { splits; eapply semantics_wf; eauto. }
  assert (events_set t ≡₁ events_set P1 ∪₁ events_set P2) as EVENTS12.
  { unfold t. unfold events_set.
    now ins; rewrite lset_app. }

  splits; auto.
  { red. unfold t, tlambda; ins.
    split; ins; desf. now apply EQLAB. }
  
  { unfold tlambda. ins. desf. }
  { unfold tlambda. ins. desf. now apply EQLAB. }

  { unfold set_disjoint, lset. ins.
    rewrite theta_map_fst, filter_list_minus, in_list_minus in IN.
    destruct IN as [IN_l' NIN_l].
    apply NIN_l, in_filter_iff; splits; auto.
    apply in_filter_iff in IN_l'; desf. }

  1,2: ins; apply wf_pt_family_equiv_on_E; auto.
  1,2: rewrite EVENTS12; clear; basic_solver.
Qed.

Lemma partial_wf :
  << WF_PT : forall D,  predTransformer (τ P12 D) >> /\
  << WF_LPT : forall D φ (CONS : lconsistent t (τ P12 D φ)), lconsistent P12 φ >> /\
  << WF_PT_SE_INDEP : forall φ e_ext v D (NOTINE : ~ (events_set P12 e_ext)),
        Formula.subst_ereg_val (τ P12 D φ) e_ext v
        ⇔
        τ t D (Formula.subst_ereg_val φ e_ext v) >> /\
  << WF_PT_FAMILY      : forall D C (CED : (C ∩₁ E) ⊆₁ D) ψ, τ P12 C ψ ⊨ τ P12 D ψ >> /\
  << WF_TERM           : term P12 ⊨ τ P12 E (Formula.tt) >> /\
  << WF_NINEλ : forall e (NIN : ~ E e), λ P12 e = def_action >> /\
  << WF_NINEκ : forall e (NIN : ~ E e), κ P12 e ⇔ Formula.tt >>.
Proof using PE1 PE2 EQLAB EQ.
  cdes props. subst.

  unfold t; subst E. splits; ins.
  all: unfold events_set in *; ins.
  { eapply pt_compose; [apply _WF1|apply _WF2]. }
  { unfold lconsistent in *; ins.

    (* (* Substitute λ12 with λ0 *) *)
    (* erewrite theta_lbl_eqdom in CONS. *)
    (* erewrite theta_lbl_eqdom. *)
    (* 2,3: by unfold eq_dom; intros; rewrite SAMELBL_12_0. *)

    (* Rewrite: P1 ∪ P2  -->  P1 ∪ (P2 \ P1) *)
    rewrite subst_ereg_val_list_eqv_func_lists
      with (l' := θ (events P1 ++ (events P2 -- events P1)) tlambda)
      in CONS; [| by apply theta_func_list |].
    2: { rewrite !theta_app, !theta_list_minus,
         !lset_app, !lset_list_minus; auto.
         rewrite set_unionC, <- set_minus_union_same.
         basic_solver. }
    rewrite theta_app, subst_ereg_val_list_app in CONS.
    rewrite wf_pt_se_indep_list with (P := P1) in CONS; auto.

    (* Substitute λ12 with λ1 to apply wf_lpt *)
    erewrite theta_lbl_eqdom with (l := events P1) in CONS.
    2: { unfold eq_dom; intros; rewrite <- _SAMELBL_12_1; eauto. }

    eapply wf_lpt in CONS; auto.
    2: by apply _SDP.

    unfold lconsistent in CONS.
    erewrite theta_lbl_eqdom with (l := events P1) in CONS.
    2: { unfold eq_dom; intros; rewrite _SAMELBL_12_1; eauto. }

    rewrite <- subst_ereg_val_list_app, <- theta_app in CONS.
    rewrite subst_ereg_val_list_eqv_func_lists
      with (l' := θ (events P2 ++ (events P1 -- events P2)) tlambda)
      in CONS; [| by apply theta_func_list |].
    2: { rewrite !theta_app, !theta_list_minus, !lset_app, !lset_list_minus; auto.
         unfolder; split; ins; desf; tauto. }
    rewrite theta_app, subst_ereg_val_list_app in CONS.
    rewrite wf_pt_se_indep_list with (P := P2) in CONS; auto.
    2: now apply _SDP.

    erewrite theta_lbl_eqdom with (l := events P2) in CONS.
    2: { unfold eq_dom; intros; rewrite <- _SAMELBL_12_2; eauto. }

    eapply wf_lpt in CONS; auto.
    unfold lconsistent in CONS.
    erewrite theta_lbl_eqdom with (l := events P2) in CONS.
    2: { unfold eq_dom; intros; rewrite <- _SAMELBL_12_2; eauto. }

    rewrite <- subst_ereg_val_list_app, <- theta_app in CONS.

    rewrite subst_ereg_val_list_eqv_func_lists
      with (l' := θ (events P1 ++ events P2) tlambda)
      in CONS; [| by apply theta_func_list |]; auto.
    rewrite !theta_app, !theta_list_minus, !lset_app, !lset_list_minus; auto.
    unfolder; split; ins; desf; tauto. }
  { rewrite wf_pt_se_indep; auto.
    1: apply pt_more; [apply _WF1 | apply wf_pt_se_indep]; auto.
    all: intro QQ; apply NOTINE; apply lset_app; basic_solver. }

  { transitivity (τ P1 C (τ P2 D ψ)).
    { eapply pt_entails; [by apply _WF1 |].
      eapply wf_pt_family; eauto.
      rewrite <- CED.
      unfold events_set; simpls.
      rewrite lset_app; basic_solver. }
    eapply wf_pt_family; eauto.
    rewrite <- CED.
    unfold events_set; simpls.
    rewrite lset_app; basic_solver. }
  { apply entails_elim_conj_l2.
    etransitivity.
    2: { apply pt_entails; [by apply _WF1|].
         etransitivity; [by apply (wf_term _WF2)|].
         eapply wf_pt_family; eauto.
         rewrite lset_app. basic_solver. }
    eapply wf_pt_family; eauto.
    rewrite lset_app. basic_solver. }
  { unfold tlambda; ins; desf.
    all: apply wf_ninEλ; auto.
    all: intros HH; apply NIN; apply lset_app; basic_solver. }
  unfold seq_κ_def. desf.
  all: exfalso; apply NIN; apply lset_app; red; auto.
Qed.

End Internal.

End SeqBuilder.
