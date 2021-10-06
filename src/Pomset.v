From hahn Require Import Hahn.
From imm Require Import Events.
From imm Require Import Prog.
From imm Require Import ProgToExecution.

Require Import Action.
Require Import Formula.
Import Formula.Properties.
Import Formula.Syntax.
Require Import PredTransformer.
Require Import AuxDef.
Require Import AuxRel.
Require Import Language.
Require Import Events.
Require Import Coq.Program.Basics.

Open Scope program_scope.

Set Implicit Arguments.

(** In this file we define Pomsets with Predicate Transformers (PwT).
    The definition comprises three main parts:

    * Record pomset defines PwTs substantively
      as a tuple of several components.

    * Record wf (well-formedness) defines the required properties
      that should hold for components of any PwT.

    * Record cand (candidate) 
*)


(* This record corresponds to Definition 4.4.
   It defines PwT as a tuple (𝐸, 𝜆, 𝜅, 𝜏 , ✓, ⊴, rf, rmw).
   Notice that in paper, rf is added 
 *)
Record pomset := {
  (* M1 *)
  events : list Event.t;

  (* M2 *)
  λ : Event.t -> action;

  (* M3 *)
  κ : Event.t -> Formula.t;

  (* M4 *)
  τ : (Event.t -> Prop) -> Formula.t -> Formula.t;

  (* M5 *)
  (* Termination condition ✓ *)
  term   : Formula.t;

  (* M6 *)
  (* Dependency order ⊴ *)
  dep    : relation Event.t;
  }.

Definition events_set P := lset (events P).

Section PomsetRelations.
Local Open Scope formula_scope.

Variable P : pomset.
Variable P' : pomset.

Let E  := (events_set P ).
Let E' := (events_set P').
Let Tid_ t := (fun x => α (λ P x) = t).
Let Tid_' t := (fun x => α (λ P' x) = t).

Record pomset_equiv :=
  {
  events_equiv  : E ≡₁ E';
  labels_equiv  : func_equiv (λ P) (λ P');
  κ_equiv       : forall e, κ P e ⇔ κ P' e;
  pt_equiv      : forall (e_set : Event.t -> Prop) (φ : Formula.t),
                             (τ P) e_set φ ⇔ (τ P') e_set φ;
  term_equiv    : term P ⇔ term P';
  dep_equiv     : dep    P ≡ dep    P';
  }.

Record pomset_superset :=
  {
  sup_acts_set : E' ⊆₁ E ;
  sup_λ        : forall e (EE : E' e), λ P' e = λ P e;
  sup_κ        : forall e (EE : E' e), κ P' e = κ P e;

  (* TODO: should e_eset be used? *)
  sup_τ        : forall e_set φ, e_set ⊆₁ E' -> τ P' φ = τ P φ;
  sup_dep      : dep P' ⊆ dep P;
  }.

Record thread_restricted_pomset (α : thread_id) :=
  {
  tr_acts_set : E' ≡₁ E ∩₁ Tid_ α;
  tr_superset : pomset_superset
  }.

End PomsetRelations.

Add Morphism events_set with signature
    pomset_equiv ==> eq ==> iff as events_set_more.
Proof. intros x y HH e. by split; ins; apply HH. Qed.

Lemma pomset_equiv_reflexive : reflexive pomset_equiv.
Proof.
  intro P.
  split; auto.
  1: ins.
  all: by split; apply entails_refl.
Qed.

Ltac pomset_equiv_rewrite :=
  repeat match goal with
         | EQ : pomset_equiv _ _ |- _ =>
           rewrite (events_equiv EQ); auto
         | EQ : pomset_equiv _ _ |- _ =>
           rewrite (labels_equiv EQ); auto
         | EQ : pomset_equiv _ _ |- _ =>
           rewrite (pt_equiv EQ); auto
         | EQ : pomset_equiv _ _ |- _ =>
           rewrite (term_equiv EQ)
         | EQ : pomset_equiv _ _ |- _ =>
           rewrite (dep_equiv EQ)
         | EQ : pomset_equiv _ _ |- _ =>
           rewrite (κ_equiv EQ)
         end.

Lemma pomset_equiv_symmetric : symmetric pomset_equiv.
Proof.
  red. ins.
  constructor; unfold func_equiv; ins; pomset_equiv_rewrite; reflexivity.
Qed.

Lemma pomset_equiv_transitive : transitive pomset_equiv.
Proof.
  red. intros x y z XY YZ. constructor.
  all: try by etransitivity; [by apply XY|]; apply YZ.
  unfold func_equiv; ins; pomset_equiv_rewrite; reflexivity.
Qed.

Add Relation pomset pomset_equiv
    reflexivity  proved by pomset_equiv_reflexive
    symmetry     proved by pomset_equiv_symmetric
    transitivity proved by pomset_equiv_transitive
      as pomset_equiv_rel.

Section Pomset.
Local Open Scope formula_scope.
(* Local Open Scope auxdef_scope. *)

Variable P : pomset.

Notation "'E'" := (events_set P).

(* TODO: can it be done using implicits? *)
Notation "'λ'" := (λ P).
Notation "'τ'" := (τ P).
Notation "'κ'" := (κ P).
Notation "'term'" := (term P).

Notation "'dep'" := (dep P).

Notation "e1 ⊴ e2" := (dep e1 e2) (at level 14).

Notation "'R'" := (fun a => is_r' (λ a)).
Notation "'W'" := (fun a => is_w' (λ a)).

Definition θ' := List.fold_left
                  (fun ψ e => match imm_lbl (λ e) with
                           | Aload _ _ _ v =>
                             Formula.eqEE (Expr.ereg e) (Expr.val v) ∧ ψ
                           | _ => ψ
                           end)
                  (events P)
                  Formula.tt.


Definition θ (events_l : list Event.t) lbl := List.flat_map
                               (fun e => match imm_lbl (lbl e) with
                                      | Aload _ _ _ v => [(e, v)]
                                      | _ => []
                                      end)
                               events_l.

Definition lconsistent φ :=
  Formula.satisfiable (Formula.subst_ereg_val_list φ (θ (events P) λ)).

Lemma tautology_lconsistent φ
      (TAUT : Formula.tautology φ) :
  lconsistent φ.
Proof.
  by apply taut_satisfiable, taut_subst_ereg_val_list.
Qed.

Lemma lconsistent_disj φ ψ (LCONS : lconsistent φ \/ lconsistent ψ) :
  lconsistent (φ ∨ ψ).
Proof using.
  red. rewrite subst_ereg_val_list_alt.
  apply sat_disj, LCONS.
Qed.

Lemma q_lconsistent x :
  lconsistent (Formula.q x).
Proof.
  unfold lconsistent.
  rewrite subst_ereg_val_list_alt.
  apply sat_q.
Qed.

Lemma theta_func_list events_l lbl:
  func_list (θ events_l lbl).
Proof.
  unfold θ. red; ins.
  apply in_flat_map in IN, IN'.
  desf; ins; desf; ins; subst.
  congruence.
Qed.

Lemma theta_app l l' lbl :
  θ (l ++ l') lbl = θ l lbl ++ θ l' lbl.
Proof.
  unfold θ. by rewrite flat_map_app.
Qed.


Open Scope list_additional_scope.

Lemma theta_list_minus l l' lbl :
  θ (l -- l') lbl = θ l lbl -- θ l' lbl.
Proof using.
  generalize dependent l'. induction l; ins.
  destruct (classic (In a l')) as [IN|NIN].
  { rewrite list_minus_cons_in; auto. desf. unfold app.
    rewrite list_minus_cons_in; auto.
    unfold θ. apply in_flat_map. eexists. splits; eauto.
    desf. }
  rewrite list_minus_cons_nin; auto. desf; ins; desf; ins.
  rewrite list_minus_cons_nin; auto.
  { by rewrite IHl. }
  intros HH. apply in_flat_map in HH. desf. inv HH0.
Qed.

Lemma theta_lbl_eqdom l lbl lbl'
      (EQDOM : eq_dom (lset l) lbl lbl') :
  θ l lbl = θ l lbl'.
Proof using.
  unfold θ.
  rewrite !flat_map_concat_map.
  erewrite map_eq_dom; eauto.
  unfold eq_dom in *; ins; desf.
  all: rewrite EQDOM in Heq; eauto; rewrite Heq in Heq0; basic_solver.
Qed.

Lemma theta_map_fst l lbl :
  map fst (θ l lbl) = filter (is_r (imm_lbl ∘ lbl)) l.
Proof.
  induction l; ins; desf. 
  { rewrite map_app; ins.
    rewrite IHl; auto. }
  all: by unfold compose, is_r in Heq0; ins; desf.
Qed.

Record wf :=
  {
    (* M3a *)
    (* wf_precondition_lconsistent : forall e, lconsistent (κ e); *)

    (* M4 *)
    wf_pt : forall D,  predTransformer (τ D);
    wf_lpt : forall D φ (CONS : lconsistent (τ D φ)), lconsistent φ;

    wf_pt_se_indep : forall φ e_ext v D (NOTINE : ~ (events_set P e_ext)),
        Formula.subst_ereg_val (τ D φ) e_ext v
        ⇔
        τ D (Formula.subst_ereg_val φ e_ext v);

    (* wf_kappa_se_indep : forall e e_ext v (NOTINE : ~ (events_set P e_ext)), *)
    (*            Formula.subst_ereg_val (κ e) e_ext v ⇔ κ e; *)

    wf_pt_family : forall D C (CED : (C ∩₁ E) ⊆₁ D) ψ, τ C ψ ⊨ τ D ψ;

    (* M5a *)
    wf_term : term ⊨ τ E (Formula.tt);

    (* M6 *)
    wf_dep_pord    : strict_partial_order dep;
    wf_depE        : dep ≡ ⦗E⦘ ⨾ dep ⨾ ⦗E⦘;


    wf_ninEλ : forall e (NIN : ~ E e), λ e = def_action;
    wf_ninEκ : forall e (NIN : ~ E e), κ e ⇔ Formula.tt;
  }.

Lemma wf_pt_family_subset (WF : wf) D C (EQ : C ⊆₁ D) ψ: τ C ψ ⊨ τ D ψ.
Proof using.
  apply wf_pt_family; auto; generalize EQ; basic_solver.
Qed.

Lemma wf_pt_family_equiv (WF : wf) D C (EQ : C ≡₁ D) ψ: τ C ψ ⇔ τ D ψ.
Proof using.
  by split; apply wf_pt_family_subset, EQ.
Qed.

Lemma wf_pt_family_equiv_on_E (WF : wf) D C ψ
      (EQ : C ∩₁ E ≡₁ D ∩₁ E):
  τ C ψ ⇔ τ D ψ.
Proof using.

  split; apply wf_pt_family; auto.
  { rewrite EQ; basic_solver. }
 rewrite <- EQ; basic_solver.
Qed.


Lemma wf_pt_se_indep_list φ l D
      (WF : wf)
      (NOTINE : set_disjoint (lset (map fst l)) (events_set P)) :
  Formula.subst_ereg_val_list (τ D φ) l
  ⇔
  τ D (Formula.subst_ereg_val_list φ l).
Proof.
  ins.
  induction l; ins; desf.
  { reflexivity. }
  rewrite IHl, wf_pt_se_indep; auto.
  { reflexivity. }
  { intros HH. eapply NOTINE; [|by apply HH].
    red. by constructor. }
  red; ins. eapply NOTINE; eauto.
  red. by constructor.
Qed.

Record cand :=
  { cand_wf : wf;

    (* C3 *)
    cand_precondition : forall e, E e -> Formula.tautology (κ e);

    (* C5 *)
    cand_termination : Formula.tautology term;

  }.

End Pomset.

Definition init_pomset : pomset :=
  {| events := nil;
     λ := fun _ => def_action;
     κ := fun _ => Formula.tt;
     τ := fun _ φ => φ;
     term   := Formula.tt;
     dep    := ∅₂;
  |}.

Lemma wf_init_pomset : wf init_pomset.
Proof.
  unfold init_pomset.
  constructor; ins; try reflexivity.
  all: try by apply strict_partial_order_empty.
  all: try basic_solver 1.
  (* { apply tautology_lconsistent. taut_solver. } *)
  constructor; ins; reflexivity.
Qed.


Definition local_initialized_pomset (regs : list Reg.t) : pomset :=
  {|  events := nil;
      λ := fun _ => mk_action (Afence Opln) tid_init;
      κ := fun _ => Formula.tt;
      τ := fun _ φ => List.fold_left
                        (fun ψ r => Formula.subst_reg ψ r (Expr.val 0)) regs φ;
      term   := Formula.ff;
      dep    := ∅₂;
  |}.

Add Morphism lconsistent with signature
  eq ==> Formula.equiv ==> iff as lconsistent_more.
Proof.
  ins; desf.
  unfold lconsistent. apply satisfiable_more.
  apply subst_ereg_val_list_more; auto.
Qed.

Add Morphism lconsistent with signature
  eq ==> Formula.entails ==> Basics.impl as lconsistent_mori.
Proof.
  ins; desf.
  unfold lconsistent. apply satisfiable_mori.
  apply subst_ereg_val_list_mori; auto.
Qed.

Lemma pomset_equiv_lset_θ x y (EQ : pomset_equiv x y) :
  lset (θ (events x) (λ x)) ≡₁ lset (θ (events y) (λ y)).
Proof.
  set (QE := pomset_equiv_symmetric EQ).
  unfold lset, θ. split; intros p HH; apply in_flat_map.
  all: apply in_flat_map in HH; destruct HH as [q [IN LL]].
  all: exists q; split; desf.
  all: try by apply (events_equiv QE).
  all: try by rewrite (labels_equiv EQ) in *;
    match goal with
    | H : imm_lbl (λ _ _) = _,
      N : imm_lbl (λ _ _) = _ |- _ => rewrite H in N; inv H
    end.
Qed.

Lemma generalized_lconsistent_more x y ϕ ψ
      (EQ : pomset_equiv x y)
      (EQF : Formula.equiv ϕ ψ) :
  lconsistent x ϕ <-> lconsistent y ψ.
Proof.
  ins; desf.
  unfold lconsistent. apply satisfiable_more.
  erewrite subst_ereg_val_list_eqv_func_lists with (l' := θ (events y) (λ y)).
  { rewrite EQF. reflexivity. }
  { apply theta_func_list. }
    by apply pomset_equiv_lset_θ.
Qed.

Lemma pomset_equiv_pt x y (EQ : pomset_equiv x y) D:
    predTransformer (τ x D) <-> predTransformer (τ y D).
Proof.
  enough (forall x y (EQ : pomset_equiv y x)
                 (HH : predTransformer (τ x D)),
             predTransformer (τ y D)) as AA.
  { split; apply AA; auto. by apply pomset_equiv_symmetric. }
  clear. ins. constructor; ins.
  all: by pomset_equiv_rewrite; apply HH.
Qed.

Add Morphism wf with signature
  pomset_equiv ==> iff as wf_more.
Proof.
  enough (forall x y (EQ : pomset_equiv y x) (WF : wf x), wf y) as AA.
  { split; intros HH; eapply AA in HH; eauto. by symmetry. }
  ins.
  
  assert (forall r, (λ y ⋄ r) ≡ (λ x ⋄ r)) as OL.
  { ins. unfolder. split; ins; pomset_equiv_rewrite.
    symmetry in EQ. pomset_equiv_rewrite. }

  constructor; ins; pomset_equiv_rewrite; try apply WF.

  all: try by (rewrite OL; apply WF).
  all: try by match goal with
              | |- strict_partial_order _ => 
                unfold strict_partial_order; pomset_equiv_rewrite; apply WF
              end.

  { by eapply pomset_equiv_pt; try apply WF. }
  2: by intro AA; apply NOTINE, EQ.

  4-5: by intros AA; apply NIN; apply EQ.
  3: { etransitivity; [by apply WF|].
       apply wf_pt_family; auto.
       pomset_equiv_rewrite. basic_solver. }
  2: by rewrite <- events_equiv; eauto.

  eapply generalized_lconsistent_more; eauto.
  { reflexivity. }
  eapply WF.
  eapply generalized_lconsistent_more; eauto.
  { eby symmetry. }
  symmetry. apply EQ.
Qed.
