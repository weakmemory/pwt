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
Require Import Events.

Set Implicit Arguments.

Local Open Scope formula_scope.

Section Semantics.
(* Local Open Scope auxdef_scope. *)

Variable P P1 P2 : pomset.

Let E := events_set P.
Let E_list := events P.
Let E1 := events_set P1.
Let E2 := events_set P2.

Let λ1 := λ P1.
Let λ2 := λ P2.
Let λ := λ P.

Let τ1 := τ P1.
Let τ2 := τ P2.
Let τ := τ P.

Let κ1 := κ P1.
Let κ2 := κ P2.
Let κ := κ P.

Let term1 := term P1.
Let term2 := term P2.
Let term := term P.

Let dep1 := dep P1.
Let dep2 := dep P2.
Let dep := dep P.

Let sync1 := sync P1.
Let sync2 := sync P2.
Let sync := sync P.

Let perloc1 := perloc P1.
Let perloc2 := perloc P2.
Let perloc := perloc P.

Let rf1 := rf P1.
Let rf2 := rf P2.
Let rf := rf P.

Let rmw1 := rmw P1.
Let rmw2 := rmw P2.
Let rmw := rmw P.

Notation "'R'" := (fun a => is_r' (λ a)).
Notation "'W'" := (fun a => is_w' (λ a)).
Notation "'F'" := (fun a => is_f' (λ a)).

Record pomset_union :=
  { events_union    : E ≡₁ E1 ∪₁ E2;
    dep_restr1      : restr_rel E1 dep    ≡ dep1;
    dep_restr2      : restr_rel E2 dep    ≡ dep2;
    sync_restr1     : restr_rel E1 sync   ≡ sync1;
    sync_restr2     : restr_rel E2 sync   ≡ sync2;
    perloc_restr1   : restr_rel E1 perloc ≡ perloc1;
    perloc_restr2   : restr_rel E2 perloc ≡ perloc2;
    rf_restr1       : restr_rel E1 rf     ≡ rf1;
    rf_restr2       : restr_rel E2 rf     ≡ rf2;
    rmw_union       : rmw                 ≡ rmw1 ∪ rmw2;
  }.

Lemma dep_union (PU : pomset_union) : dep1 ∪ dep2 ⊆ dep.
Proof using.
  rewrite <- dep_restr1, <- dep_restr2; auto.
  basic_solver.
Qed.

Lemma sync_union (PU : pomset_union) : sync1 ∪ sync2 ⊆ sync.
Proof using.
  rewrite <- sync_restr1, <- sync_restr2; auto.
  basic_solver.
Qed.

Lemma perloc_union (PU : pomset_union) : perloc1 ∪ perloc2 ⊆ perloc.
Proof using.
  rewrite <- perloc_restr1, <- perloc_restr2; auto.
  basic_solver.
Qed.

Lemma rf_union (PU : pomset_union) : rf1 ∪ rf2 ⊆ rf.
Proof using.
  rewrite <- rf_restr1, <- rf_restr2; auto.
  basic_solver.
Qed.

Definition label_union := forall e, (E1 e -> λ e = λ1 e) /\ (E2 e -> λ e = λ2 e).

Record SKIP :=
  { skip_events : E ≡₁ ∅;
    skip_pt     : forall D ψ, τ D ψ ⇔ ψ;
    skip_term   : term   ⇔ Formula.tt;
    skip_dep    : dep    ≡ ∅₂;
    skip_perloc : perloc ≡ ∅₂;
    skip_sync   : sync   ≡ ∅₂;
    skip_rmw    : rmw    ≡ ∅₂;
    skip_rf     : rf     ≡ ∅₂;
    skip_κ      : forall e, κ e ⇔ Formula.tt;
    skip_λ      : forall e, λ e = def_action;
  }.

Record PAR :=
  {
    (* P1 P6 P7 P8 P9 *)
    par_pomset_union : pomset_union;

    (* P1 *)
    par_events_disj : set_disjoint E1 E2;

    (* P2 *)
    par_label_union : label_union;

    (* P3 *)
    par_precondition : forall e, (E1 e -> κ e ⇔ κ1 e) /\
                            (E2 e -> κ e ⇔ κ2 e);
    (* P4 *)
    par_pt : τ = τ1;

    (* P5 *)
    par_term : term = term1 ∧ term2;

    par_wf : wf P;
  }.

Definition seq_κ_def l dep_rel (e : Event.t) :=
            let pref  :=
                ifP is_r' (l e)
                then E1
                else prefix dep_rel (eq e)
            in
            ifP E2 e
            then
              (ifP E1 e
               then κ1 e
               else Formula.ff)
              ∨ τ1 pref (κ2 e)
            else
              ifP E1 e
              then κ1 e
              else Formula.tt.

Record SEQ :=
  {
    (* S1 S6 S8 S9 *)
    seq_pomset_union : pomset_union;

    (* S2 *)
    seq_label_union : label_union;
    (* seq_label_union : forall e, ((E1 \₁ E2) e -> λ e = λ1 e) /\ *)
    (*                            ((E2 \₁ E1) e -> λ e = λ2 e) /\ *)
    (*                            ((E1 ∩₁ E2) e -> merge (λ1 e) (λ2 e) (λ e)); *)

    (* S3 *)
    seq_κ : forall e, κ e ⇔ seq_κ_def λ dep e;

    (* seq_precondition : forall e, *)
    (*     let pref  := (prefix (dep \ eq) ((eq e) ∩₁ (W ∪₁ F))) *)
    (*                    ∪₁ dom_rel (E1 × ((eq e) ∩₁ R)) in *)
    (*     let κ2'e  := τ1 pref (κ2 e) in *)
    (*     << EK1  : (E1 \₁ E2) e -> κ e ⇔ κ1 e >> /\ *)
    (*     << EK2  : (E2 \₁ E1) e -> κ e ⇔ κ2'e >> /\ *)
    (*     << EK12 : (E1 ∩₁ E2) e -> κ e ⇔ (κ1 e ∨ κ2'e) >>; *)

    (* S4 *)
    seq_pt : forall D ψ, τ D ψ ⇔ τ1 D (τ2 D ψ);

    (* S5 *)
    seq_term : term ⇔ term1 ∧ τ1 E1 term2;

    (* S7a *)
    seq_sync_delay : forall d e (E1D : E1 d) (E2D : E2 e)
                            (SYNC : sync_delays (λ1 d) (λ2 e)),
        (sync)^? d e;

    (* S8a *)
    seq_coh_delay : forall d e (E1D : E1 d) (E2D : E2 e)
                           (COH : coh_delays (λ1 d) (λ2 e)),
        (perloc)^? d e;

    seq_wf  : wf P;
    seq_wf1 : wf P1;
  }.

Definition if_κ_def φ (e : Event.t) :=
            ifP E2 e
            then
              ifP E1 e
              then (φ ∧ (κ1 e)) ∨ ((¬ φ) ∧ κ2 e)
              else (¬ φ) ∧ κ2 e
            else
              ifP E1 e
              then φ ∧ κ1 e
              else Formula.tt.

Record IFF (φ : Formula.t) :=
  {
    (* I1 I6 I8 I9 *)
    if_pomset_union : pomset_union;

    (* I2 *)
    if_label_union : label_union;

    (* I3 *)
    if_κ : forall e, κ e ⇔ if_κ_def φ e;

    (* I4 *)
    if_pt : forall D ψ, τ D ψ ⇔ (φ ∧ (τ1 D ψ)) ∨ ((¬ φ) ∧ (τ2 D ψ));

    (* I5 *)
    if_term : term ⇔ (φ ∧ term1) ∨ ((¬ φ) ∧ term2);

    if_wf : wf P;
  }.

Record LETT (r : Reg.t) (m : Expr.t) :=
  { let_events : E ≡₁ ∅;
    let_pt     : forall D ψ, τ D ψ ⇔ Formula.subst_reg ψ r m;
    let_term   : term     ⇔ Formula.tt;
    let_dep    : dep      ≡ ∅₂;
    let_perloc : perloc   ≡ ∅₂;
    let_sync   : sync     ≡ ∅₂;
    let_rmw    : rmw      ≡ ∅₂;
    let_rf     : rf       ≡ ∅₂;
    let_κ      : forall e, κ e ⇔ Formula.tt;
    let_noereg : Expr.no_eregs m;
    let_λ      : forall e, λ e = def_action;
  }.

Definition zero_or_one_event := E × E ⊆ eq.

Record FENCE (α : thread_id) (μ : mode) :=
  {
    (* F1 *)
    fence_events : zero_or_one_event;

    (* F2 *)
    fence_λ      : λ = fun e =>
                       ifP E e
                       then {| imm_lbl:=Afence μ; α:=α; |}
                       else def_action;

    (* F3 *)
    fence_κ : forall e, κ e ⇔ Formula.tt;

    (* F4 *)
    fence_pt : forall D ψ, τ D ψ ⇔ ψ;

    (* F5 *)
    fence_term : term ⇔ ifP E ≡₁ ∅
                        then Formula.ff
                        else Formula.tt;

    fence_dep    : dep    ≡ ∅₂;
    fence_perloc : perloc ≡ ∅₂;
    fence_sync   : sync   ≡ ∅₂;
    fence_rmw    : rmw    ≡ ∅₂;
    fence_rf     : rf     ≡ ∅₂;
  }.

Let κE := Formula.disj_list (map κ E_list).

Definition read_κ_def x e :=
  ifP E e then Formula.q x else Formula.tt.

Definition read_τ_def r x v ϕ D ψ s :=
  let dep_case e :=
      ϕ e ⇒
        ((Formula.q x ⇒ (Formula.eqEE (Expr.val (v e)) (Expr.ereg e)))
         ⇒
         Formula.subst_reg ψ r (Expr.ereg e))
  in
  let indep_case e :=
      ϕ e ⇒
        (((Formula.q x ⇒
          ((Formula.eqEE (Expr.val (v e)) (Expr.ereg e)) ∨
           (Formula.eqLE x (Expr.ereg e)))))
        ⇒
        Formula.subst_reg ψ r (Expr.ereg e))
  in
  Formula.conj_list (map dep_case (filterP D E_list)) ∧
  Formula.conj_list (map indep_case (filterP (set_compl D) E_list)) ∧
  (Formula.conj_list (map (fun e => ¬ (ϕ e)) E_list) ⇒
   Formula.subst_reg ψ r (Expr.reg s)).

Record READ (α : thread_id) (r : Reg.t)
       (μ : mode) (x : location)
       (v : Events.Event.t -> Events.value)
       (ϕ : Events.Event.t -> Formula.t) :=
{

  (* R1 *)
  read_events : forall e d (INe : E e) (INd : E d)
                  (SAT : Formula.satisfiable (ϕ e ∧ ϕ d)),
                e = d;

  (* R2 *)
  read_λ      : λ = fun e =>
                      ifP E e
                      then {| imm_lbl:=Aload false μ x (v e); α:=α; |}
                      else def_action;

  (* R3 *)
  read_κ : forall e, κ e ⊨ read_κ_def x e;

  read_κ_nE : forall e (NIN : ~ E e), κ e ⇔ Formula.tt;

  (* R4 *)
  read_pt : forall D ψ s,
      τ D ψ ⇔ read_τ_def r x v ϕ D ψ s;

  read_term : term ⇔ ifP mode_le Oacq μ /\ E ≡₁ ∅
                      then κE
                      else Formula.tt;

  read_dep    : dep    ≡ ∅₂;
  read_perloc : perloc ≡ ∅₂;
  read_sync   : sync   ≡ ∅₂;
  read_rmw    : rmw    ≡ ∅₂;
  read_rf     : rf     ≡ ∅₂;

  read_ϕ_ereg : forall e, Formula.used_eregs (ϕ e) = nil;
}.

Definition write_κ_def m v e :=
  ifP E e then Formula.eqEE m (Expr.val (v e)) else Formula.tt.

Record WRITE (α : thread_id) (x : location)
       (m : Expr.t) (μ : mode) (v : Events.Event.t -> Events.value) := {
  (* W1 *)
  (* if κ (d) ∧ κ (e) is satisfiable then d = e, *)
  write_events : forall e d (INe : E e) (INd : E d)
                   (SAT : Formula.satisfiable (κ e ∧ κ d)),
                 e = d;

  (* W2 *)
  write_λ      : λ = fun e =>
                       ifP E e
                       then {| imm_lbl:=Astore Xpln μ x (v e); α:=α; |}
                       else def_action;

  (* W3 *)
  write_κ : forall e, κ e ⊨ write_κ_def m v e;
  write_κ_nE : forall e (NIN : ~ E e), κ e ⇔ Formula.tt;
  write_κ_ereg : forall e e_ext v,
      Formula.subst_ereg_val (κ e) e_ext v ⇔ κ e;

  (* W4 *)
  write_pt : forall D ψ,
      τ D ψ ⇔ (Formula.subst_q
                 (Formula.subst_loc ψ x m)
                 x
                 κE);

  (* W5 *)
  write_term : term ⇔ κE;

  write_dep    : dep    ≡ ∅₂;
  write_perloc : perloc ≡ ∅₂;
  write_sync   : sync   ≡ ∅₂;
  write_rmw    : rmw    ≡ ∅₂;
  write_rf     : rf     ≡ ∅₂;

  write_noereg : Expr.no_eregs m;
  write_sat    : forall e (IN : E e),
      Formula.satisfiable (Formula.eqEE m (Expr.val (v e)));
  }.

End Semantics.

(* Semantic brackets relation *)
(* TODO: what about  CAS, FADD, and EXCHG? *)
(* TODO: Can it be simplified using pattern matching? *)
Inductive Semantics (α : thread_id) (s : Stmt.t) (P : pomset) : Prop :=

| interp_skip (stmt_eq : s = Stmt.skip) (PE : SKIP P)

(* TODO: get rid of lambda *)
| interp_assign r m
                (stmt_eq : s = Stmt.assign r m)
                (PE : LETT P r m)

| interp_read r x μ v ϕ
              (stmt_eq : s = Stmt.read r x μ)
              (PE : READ P α r μ x v ϕ)

| interp_write x μ m v
              (stmt_eq : s = Stmt.write x μ m)
              (PE : WRITE P α x m μ v)

| interp_fence μ
              (stmt_eq : s = Stmt.fence μ)
              (PE : FENCE P α μ)

(* | interp_par γ s1 s2 p1 p2 P1 P2 *)
(*                 (stmt_eq : s = par_st s1 s2 γ) *)
(*                 (interp1 : Semantics γ s1 p1) *)
(*                 (in_pomset1 : p1 P1) *)
(*                 (interp2 : Semantics α s2 p2) *)
(*                 (in_pomset2 : p2 P2) *)
(*                 (PE : p ≡₁ fun P => PAR P P1 P2) *)

| interp_seq s1 s2 P1 P2
            (stmt_eq : s = Stmt.seq s1 s2)
            (interp1 : Semantics α s1 P1)
            (interp2 : Semantics α s2 P2)
            (PE : SEQ P P1 P2)

| interp_if m s1 s2 P1 P2
           (stmt_eq : s = Stmt.ite m s1 s2)
           (interp1 : Semantics α s1 P1)
           (interp2 : Semantics α s2 P2)
           (PE : IFF P P1 P2 (Formula.neg (Formula.eqEE m (Expr.val 0))))
.

Ltac pomset_big_simplifier :=
  match goal with
  | PE : SKIP _ |- _ =>
    rewrite ?(skip_perloc PE), ?(skip_dep PE), ?(skip_rmw PE), ?(skip_sync PE), ?(skip_rf PE),
            ?(skip_κ PE), ?(skip_λ PE)
  | PE : LETT _ _ _ |- _ =>
    rewrite ?(let_perloc PE), ?(let_dep PE), ?(let_rmw PE), ?(let_sync PE), ?(let_rf PE),
            ?(let_κ PE), ?(let_λ PE)
  | PE : READ _ _ _ _ _ _ _ |- _ =>
    rewrite ?(read_perloc PE), ?(read_dep PE), ?(read_rmw PE), ?(read_sync PE), ?(read_rf PE),
            ?(read_κ PE), ?(read_λ PE); unfold read_κ_def
  | PE : WRITE _ _ _ _ _ _ |- _ =>
    rewrite ?(write_perloc PE), ?(write_dep PE), ?(write_rmw PE), ?(write_sync PE),
            ?(write_rf PE),
            ?(write_κ PE),
            ?(write_λ PE); unfold write_κ_def
  | PE : FENCE _ _ _ |- _ =>
    rewrite ?(fence_perloc PE), ?(fence_dep PE), ?(fence_rmw PE), ?(fence_sync PE),
            ?(fence_rf PE),
            ?(fence_κ PE),
            ?(fence_λ PE)
  end.

Ltac pomset_pt_simplifier :=
  match goal with
  | PE : SKIP _              |- _ => rewrite ?(skip_pt PE) in *
  | PE : LETT _ _ _          |- _ => rewrite ?(let_pt PE) in *
  | PE : WRITE _ _ _ _ _ _   |- _ => rewrite ?(write_pt PE) in *
  | PE : READ  _ _ _ _ _ _ _ |- _ => erewrite ?(read_pt PE) in *
  | PE : FENCE _ _ _         |- _ => rewrite ?(fence_pt PE) in *
  end.

Lemma semantics_wf (α : thread_id) (s : Stmt.t) (P : pomset) (SP : Semantics α s P)
  : wf P.
Proof.
  generalize dependent P.
  induction s; ins.
  all: inv SP; (try by apply PE); constructor; ins.
  all: pomset_big_simplifier.
  all: eauto using strict_partial_order_empty with hahn.

  (* TODO: for some reason morphism strict_partial_order_more doesn't work  *)
  all: try by match goal with
              | |- strict_partial_order _ => 
                unfold strict_partial_order; pomset_big_simplifier;
                  apply strict_partial_order_empty
              end.

  all: try by now (try constructor); ins; pomset_pt_simplifier;
    auto using entails_true, entails_resp_subst_reg, entails_resp_subst_loc.
  all: try by red; auto using taut_satisfiable, taut_subst_ereg_val_list, taut_tt.
  all: ins.
  all: try by apply PE.
  all: try basic_solver 1.

  (** LET **)
  { pomset_pt_simplifier.
    unfold lconsistent in *.
    rewrite subst_ereg_val_list_subst_reg_commute in CONS.
    { eapply sat_subst_reg; eauto. }
    unfold lset. unfolder. ins.
    rewrite Expr.no_eregs_used_eregs in IN; auto.
    apply PE. }
  { inv SP. inv PE0. rewrite !let_pt0.
    rewrite subst_ereg_val_subst_reg_commute; try easy.
    red in let_noereg0; basic_solver. }
  (** WRITE **)
  7: { pomset_pt_simplifier.
       unfold lconsistent in *.
       rewrite subst_q_subst_ereg_val_list_inject,
               subst_ereg_val_list_subst_q_commute,
               subst_ereg_val_list_subst_loc_commute in CONS.
       2: { rewrite Expr.no_eregs_used_eregs; [easy |].
            eapply write_noereg; eauto. }
       2: { apply subst_ereg_val_list_nin. }
       now apply sat_subst_q, sat_subst_loc in CONS. }
  6: { constructor; ins; rewrite !write_pt; eauto; ins; try easy.
       now apply resp_subst_q, entails_resp_subst_loc. }
  6: { rewrite !(write_pt PE); eauto.
       rewrite subst_q_subst_ereg_val_inject.
       rewrite subst_ereg_val_subst_q_commute,
               subst_ereg_val_subst_loc_commute; try easy.
       { rewrite subst_ereg_val_disj_list, map_map.
         erewrite disj_list_more; [easy |]; ins.
         apply Forall2_map_map; ins.
         now apply PE. }
       { rewrite Expr.no_eregs_used_eregs; auto.
         eapply write_noereg; eauto. }
       apply subst_ereg_val_no_ereg. }

  (** READ **)
  all: try rewrite ?(read_term PE).

  (** READ, pt **)
  { eapply pt_ext with (t := fun ψ => read_τ_def P r0 x v ϕ D ψ r0).
    2: { ins. now rewrite (read_pt PE). }
    unfold read_τ_def.
    remember (Formula.conj_list (map (fun e : Event.t => ¬ ϕ e) (events P))) as χ.
    apply pt_split_world with (χ := χ).
    { eapply pt_ext with
          (t := fun ψ =>
                  (χ ⇒ Formula.subst_reg ψ r0 (Expr.reg r0))).
      { apply impl_preserves_pt, pt_f_subst_reg. }
      ins.
      rewrite !impl_conj_r.

      assert (forall η l (SUBLIST : lset l ⊆₁ (events_set P)),
                 χ ⇒ Formula.conj_list
                   (map (fun e : Event.t => ϕ e ⇒ η e) l) ⇔ Formula.tt)
        as HELPER.
      { symmetry; apply equiv_true_taut_l.
        rewrite impl_conj_list_r, map_map.
        apply taut_conj_list, Forall_forall; intro y.
        rewrite in_map_iff.
        intros [e [QQ IN]]; desf.
        apply SUBLIST in IN.
        apply impl_impl_disjunctive_premise.
        apply taut_equiv_not_satisfiable_neg.
        rewrite <-formula_de_morgan2. 
        rewrite conj_sym, conj_spread_list_nonempty.
        2: { rewrite map_eq_nil.
             intro QQ. rewrite <- lset_empty_iff in QQ.
             now apply QQ in IN. }
        rewrite map_map, formula_de_morgan2_list, map_map.
        apply taut_disj_list, Exists_exists.
        eexists.
        split.
        { apply in_map_iff. exists e.
          now split. }
        red. red_helper; ins; desf. }
      rewrite !HELPER.
      { now rewrite !conj_true_l, impl_impl_same. }
      all: now intros e QQ; apply in_filterP_iff in QQ. }
    eapply pt_ext.
    2: { intro.
         match goal with
         |  |- _ ⇔ ?X ⇒ ?Y ∧ ?Z ∧ ?T =>
            arewrite ((X ⇒ Y ∧ Z) ⇔ (X ⇒ Y ∧ Z ∧ T))
         end.
         2: easy.
         rewrite !impl_conj_r.
         match goal with
         | [ |- context[(¬ χ) ⇒ χ ⇒ ?X] ] =>
           arewrite (((¬ χ) ⇒ χ ⇒ X) ⇔ Formula.tt)
         end.
         { symmetry.
           now apply equiv_true_taut_l, impl_impl_disjunctive_premise,
           disjunctive_neg_x_and_x. }
         now rewrite conj_true_r. }
    apply impl_preserves_pt.
    clear dependent χ.

    set (χ := Formula.disj_list
                (map (fun e : Event.t => ϕ e)
                     (filterP D (events P)))).
    apply pt_split_world with (χ := χ).
    { eapply pt_ext.
      2: { intro.
           match goal with
           |  |- _ ⇔ χ ⇒ ?Y ∧ ?Z =>
              arewrite ((χ ⇒ Y) ⇔ (χ ⇒ Y ∧ Z))
           end.
           2: easy.
           rewrite !impl_conj_r.
           match goal with
           |  |- _ ⇔ _ ∧ (χ ⇒ ?Y) =>
              arewrite ((χ ⇒ Y) ⇔ Formula.tt)
           end.
           2: { now rewrite conj_true_r. }
           symmetry. apply equiv_true_taut_l.
           rewrite impl_conj_list_r, map_map.
           apply taut_conj_list, Forall_forall; intro y.
           rewrite in_map_iff.
           intros [e [QQ IN]]; desf.
           apply impl_impl_disjunctive_premise.
           subst χ.
           rewrite disj_list_conj_distrib, map_map.
           intro QQ.
           apply sat_disj_list, Exists_exists in QQ; desf.
           apply in_map_iff in QQ; desf.
           apply in_filterP_iff in QQ1; desf.
           apply in_filterP_iff in IN; desf.
           red in IN0.
           assert (e = x2); [| basic_solver].
           eapply read_events; eauto.
           now rewrite conj_sym. }
      apply impl_preserves_pt.
      clear dependent χ.
      apply conj_list_pt.
      { red; ins. apply PE; auto.
        all: repeat match goal with
                    | H : In _ (filterP _ _) |- _ => apply in_filterP_iff in H; desf
                    end. }
      apply Forall_forall; ins.
      apply impl_preserves_pt, pt_f_subst_reg. }
    eapply pt_ext.
    2: { intro.
         match goal with
         |  |- _ ⇔ ?χ ⇒ ?Y ∧ ?Z =>
            arewrite ((χ ⇒ Z) ⇔ (χ ⇒ Y ∧ Z))
         end.
         2: easy.
         rewrite !impl_conj_r.
         match goal with
         |  |- _ ⇔ (?χ ⇒ ?Y) ∧ _ =>
            arewrite ((χ ⇒ Y) ⇔ Formula.tt)
         end.
         2: { now rewrite conj_true_l. }
         symmetry. apply equiv_true_taut_l.
         rewrite impl_conj_list_r, map_map.
         apply taut_conj_list, Forall_forall; intro y.
         rewrite in_map_iff.
         intros [e [QQ IN]]; desf.
         apply impl_impl_disjunctive_premise.
         subst χ.
         rewrite formula_de_morgan_list, map_map.
         rewrite conj_sym, conj_spread_list_nonempty, map_map.
         2: { rewrite map_eq_nil.
              intro QQ. rewrite <- lset_empty_iff in QQ.
              now apply QQ in IN. }
         intro QQ.
         apply sat_conj_list in QQ.
         rewrite Forall_forall in QQ.
         eapply disjunctive_x_and_neg_x, QQ, in_map_iff; eauto. }
    apply impl_preserves_pt.
    clear dependent χ.
    apply conj_list_pt.
    { red; ins. apply PE; auto.
      all: repeat match goal with
                  | H : In _ (filterP _ _) |- _ => apply in_filterP_iff in H; desf
                    end. }
      apply Forall_forall; ins.
      apply impl_preserves_pt, pt_f_subst_reg. }

  (* all: try (erewrite !(read_pt_empty PE _ _ _ P_EMPTY); desf; easy). *)
  (* { desf; [by apply P_EMPTY in e0 |]. *)
  (*   eapply tautology_lconsistent; taut_solver. } *)
  (** READ, non_empty case **)
  (* { desf; [ by apply q_lconsistent *)
  (*         | by apply tautology_lconsistent; taut_solver]. } *)

  all: erewrite !(read_pt PE) in *; eauto.
  4: { unfold read_τ_def in *.
       desc; ins.
       transitivity Formula.tt.
       { apply entails_true. }
       apply equiv_true_taut_l.
       repeat (apply taut_conj; split).
       3: { apply impl_taut_is_taut. apply taut_tt. }
       all: apply taut_conj_list, Forall_forall.
       all: intros ψ HH; apply in_map_iff in HH.
       all: desc; apply in_filterP_iff in HH0; desc.
       all: rewrite <- HH.
       all: repeat apply impl_taut_is_taut.
       all: apply taut_tt. }
  3: { unfold read_τ_def in *.
       rewrite !conj_assoc.
       apply conj_mori; [|easy].
       repeat (apply entails_elim_conj_r; split).
       2: { apply entails_elim_conj_l2.
            apply conj_list_inclusion.
            rewrite !lset_map. apply set_collect_mori; auto.
            rewrite !lset_filterP.
            rewrite <- CED.
            basic_solver. }
       apply entails_conj_list; intros φ IN.
       apply in_map_iff in IN. destruct IN as [e [HH IN]]; subst.
       apply in_filterP_iff in IN. destruct IN as [IN DE]; subst.
       destruct (classic (C e)) as [CE|NCE].
       { apply entails_elim_conj_l1.
         apply conj_list_entails_in, in_map_iff.
         eexists; splits; try easy.
         now apply in_filterP_iff. }
       apply entails_elim_conj_l2.
       etransitivity.
       { apply conj_list_entails_in, in_map_iff.
         eexists; splits; try easy.
         apply in_filterP_iff; eauto. }
       repeat (apply impl_mori; try easy).
       apply entails_left_disj. }
  2: { assert (forall e, Formula.subst_ereg_val (ϕ e) e_ext v0 ⇔ ϕ e)
         as NO_SUBST_EREG.
       { ins.
         rewrite nin_subst_ereg_val; [easy |].
         erewrite read_ϕ_ereg; eauto. }
       unfold read_τ_def in *; ins.
       rewrite !subst_ereg_val_conj_list, !map_map.
       repeat (apply conj_more).
       3: { rewrite subst_ereg_val_subst_reg_commute; ins.
            apply disj_more; [|easy].
            apply neg_more. apply conj_list_more.
            apply Forall2_map_map; intros e IN.
            now rewrite NO_SUBST_EREG. }
       all: apply conj_list_more.
       all: apply Forall2_map_map; intros e IN.
       all: apply in_filterP_iff in IN; desf; ins.
       all: apply disj_more.
       (* TODO: need smth about absense of unrelated eregs in ϕ? *)
       1,3: now rewrite NO_SUBST_EREG.
       all: do 2 desf.
       all: rewrite subst_ereg_val_subst_reg_commute; ins.
       all: try now intros HH; desf.
       all: now apply disj_more. }
  unfold lconsistent in *; ins.
  unfold read_τ_def in *.
  do 2 rewrite subst_ereg_val_list_conj in CONS.
  rewrite !subst_ereg_val_list_conj_list, !map_map in CONS.
  apply sat_iff in CONS; desf.
  rewrite <- conj_list_single with (φ := Formula.subst_ereg_val_list _ _) in CONS.
  rewrite <- !conj_list_app in CONS.
  rewrite eval_conj_list, !map_app, !forallb_app, !map_map in CONS.
  apply andb_prop in CONS. destruct CONS as [CONS_indep CONS].
  apply andb_prop in CONS. destruct CONS as [CONS_dep CONS_empty].
  destruct (classic
              (exists e,
                  (events_set P) e /\
                  Formula.eval locf regf eregf qf
                    (Formula.subst_ereg_val_list (ϕ e) (θ (events P) (λ P))) = true))
           as [[e [Ee eval_e]] | EMPTY].
  { assert (In (e, v e) (θ (events P) (λ P))) as ev_in_θ.
    { unfold θ.
      apply in_flat_map_Exists, Exists_exists. exists e.
      splits; [done |].
      rewrite (read_λ PE); desf.
      basic_solver. }
    enough (exists ψ (F : Event.t -> Prop)
              (TAUT_ψ : Formula.tautology
                          (Formula.subst_ereg_val (ψ e) e (v e)))
              (F_e : F e),
               forallb id
                 (map
                    (fun x0 : Event.t =>
                     Formula.eval locf regf eregf qf
                       (Formula.subst_ereg_val_list
                          (ϕ x0
                           ⇒ (Formula.q x ⇒ (ψ x0))
                             ⇒ Formula.subst_reg φ r0 (Expr.ereg x0))
                          (θ (events P) (λ P)))) (filterP F (events P))) = true) as
        [ψ [F [TAUT_ψ [F_e QQ]]]].
    { rewrite forallb_forall in QQ.
      specialize (QQ false); unfold id in QQ.
      apply sat_iff.
      do 4 eexists.
      apply Bool.not_false_is_true.
      intro eval_false.
      apply Bool.diff_false_true, QQ.
      apply in_map_iff. exists e.
      splits; [| by apply in_filterP_iff].
      rewrite subst_ereg_val_list_impl; ins.
      rewrite eval_e; ins.
      do 2 rewrite subst_ereg_val_list_impl; ins.
      apply Bool.orb_false_intro.
      2: { rewrite <- eval_false.
           erewrite compose_subst_ereg_val_list_subst_reg with (v := v e); auto.
           { now rewrite eval_subst_reg. }
           apply theta_func_list. }
      rewrite Bool.negb_orb.
      apply Bool.andb_false_intro2.
      erewrite subst_ereg_val_list_extract with (e := e) (v := v e); ins.
      2: { apply theta_func_list. }
      desf; ins.
      apply equiv_true_taut_l in TAUT_ψ.
      rewrite <- TAUT_ψ.
      do 2 (rewrite subst_ereg_val_list_alt; ins). }

    destruct (classic (D e)) as [De | nDe].
    { exists (fun x0 => Formula.eqEE (Expr.val (v x0)) (Expr.ereg x0)).
      exists D.
      eexists; eauto.
      ins; desf; ins; taut_solver. }
    exists (fun x0 => Formula.eqEE (Expr.val (v x0)) (Expr.ereg x0)
              ∨ Formula.eqLE x (Expr.ereg x0)).
    exists (set_compl D).
    eexists; eauto.
    ins; desf; ins.
    apply taut_disj; left. taut_solver. }
  clear CONS_dep CONS_indep.
  rewrite forallb_forall in CONS_empty.
  specialize (CONS_empty false); unfold id in CONS_empty.
  apply sat_iff.
  do 4 eexists.
  apply Bool.not_false_is_true.
  intro eval_false.
  apply Bool.diff_false_true, CONS_empty.
  ins; left.
  rewrite subst_ereg_val_list_impl; ins.
  apply Bool.orb_false_intro.
  2: { now rewrite <- eval_false, subst_reg_same_reg. }
  apply Bool.negb_true_iff.
  rewrite Bool.negb_involutive,
  subst_ereg_val_list_conj_list, map_map,
  eval_conj_list, map_map.
  apply forallb_forall.
  intros y HH.
  unfold id.
  apply in_map_iff in HH; desf.
  apply Bool.not_false_is_true.
  intro x0_false.
  apply EMPTY.
  exists x0; splits; [done |].
  rewrite subst_ereg_val_list_alt in x0_false; ins.
  now apply Bool.negb_false_iff.
  Unshelve. all: easy.
Qed.

Lemma skip_init_pomset : SKIP init_pomset.
Proof.
  unfold init_pomset.
  now constructor; ins.
Qed.


Definition seq_extend (α : thread_id) (p1 : pomset -> Prop) (s : Stmt.t) (P : pomset) : Prop :=
  exists P2,
    ⟪ interp_statement : Semantics α s P2 ⟫ /\
    ⟪ seqq : exists P1, p1 P1 /\ SEQ P P1 P2 ⟫.

Add Morphism zero_or_one_event with signature
    pomset_equiv ==> iff as zero_or_one_event_more.
Proof.
  ins. unfold zero_or_one_event.
  now pomset_equiv_rewrite.
Qed.

Add Morphism SKIP with signature
  pomset_equiv ==> iff as skip_more.
Proof.
  enough (forall x y, pomset_equiv y x -> SKIP x -> SKIP y) as AA.
  { ins. now split; apply AA. }
  intros x y EQ HH; inv HH.
  constructor; ins.
  all: pomset_equiv_rewrite; try apply HH.
Qed.

Add Morphism LETT with signature
  pomset_equiv ==> eq ==> eq ==> iff as lett_more.
Proof.
  enough (forall x y r e, pomset_equiv y x -> LETT x r e -> LETT y r e) as AA.
  { ins; desf. now split; apply AA. }
  intros x y r e EQ HH; inv HH.
  constructor; ins.
  all: pomset_equiv_rewrite; try apply HH.
Qed.

Add Morphism read_τ_def with signature
    pomset_equiv ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> Formula.equiv
      as read_τ_def_more.
Proof.
  intros x y EQ; ins. unfold read_τ_def.
  repeat apply conj_more.
  3: { apply disj_more; try easy.
       apply neg_more.
       apply conj_list_equiv; rewrite !lset_map.
       apply set_collect_more; auto.
       apply EQ. }
  all: apply conj_list_equiv; rewrite !lset_map.
  all: apply set_collect_more; auto.
  all: rewrite !lset_filterP.
  all: now rewrite (events_equiv EQ).
Qed.

Add Morphism READ with signature
  pomset_equiv ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff as read_more.
Proof.
  enough (forall x y t r m l v ph,
             pomset_equiv y x -> READ x t r m l v ph -> READ y t r m l v ph) as AA.
  { ins; desf. now split; apply AA; auto. }
  intros x y t r m l v ph EQ HH; inv HH.
  constructor; ins.
  all: try by pomset_equiv_rewrite; try apply HH.
  { apply HH; auto.
    all: now rewrite <- EQ. }
  { apply functional_extensionality; ins. 
    pomset_equiv_rewrite. rewrite (read_λ HH).
    clear -EQ. desf; exfalso.
    all: match goal with
         | H : ~ events_set _ _ |- _ => apply H
         end.
    all: apply (events_equiv EQ); auto. }
  { pomset_equiv_rewrite.
    rewrite read_κ0.
    unfold read_κ_def; desf; try easy.
    all: try now apply entails_true.
    all: now exfalso; eapply n, events_equiv; eauto. }
  { pomset_equiv_rewrite. apply HH.
    now rewrite <- EQ. }
  { pomset_equiv_rewrite.
    rewrite (read_pt HH).
    now apply read_τ_def_more. }
  pomset_equiv_rewrite.
  rewrite (read_term HH).
  clear -EQ. desf; try easy.

  1-3: apply disj_list_equiv_gen; desf; ins.
  1-6: apply in_map_iff in IN; desf;
    eexists; splits; eauto; [|try (now apply EQ); now symmetry; apply EQ].
  1-6: apply in_map_iff; eexists; splits; eauto.
  1-6: now apply (events_equiv EQ).

  all: exfalso; ins; desf.
  all: match goal with
       | H : ~ _ |- _ => apply H
       end.
  all: split; auto.
  all: try rewrite <- (events_equiv EQ); auto.
  all: rewrite (events_equiv EQ); auto.
Qed.

Add Morphism write_κ_def with signature
    pomset_equiv ==> eq ==> eq ==> eq ==> Formula.equiv as write_κ_def_more.
Proof.
  intros x y EQ; ins. unfold write_κ_def. desf; try easy.
  all: exfalso; apply n.
  all: now apply EQ.
Qed.

Add Morphism WRITE with signature
  pomset_equiv ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff as write_more.
Proof.
  enough (forall x y t r m l v,
             pomset_equiv y x -> WRITE x t r m l v -> WRITE y t r m l v) as AA.
  { ins; desf. now split; apply AA. }
  intros x y t r m l v EQ HH; inv HH.

  assert (Formula.disj_list (map (κ x) (events x)) ⇔
          Formula.disj_list (map (κ y) (events y))) as XX.
  { apply disj_list_equiv_gen; ins.
    all: apply in_map_iff in IN; desf.
    all: apply EQ in IN0.
    all: eexists; splits; [|try (now apply EQ); now symmetry; apply EQ].
    all: apply in_map_iff; eauto. }

  constructor; ins.
  all: try by pomset_equiv_rewrite; try apply HH.
  7: { now apply HH; rewrite <- EQ. }
  { apply HH; auto.
    1-2: now rewrite <- EQ.
    eapply satisfiable_more; eauto.
    apply conj_more; symmetry; apply EQ. }
  { apply functional_extensionality; ins. 
    pomset_equiv_rewrite. rewrite (write_λ HH).
    clear -EQ. desf; exfalso.
    all: match goal with
         | H : ~ events_set _ _ |- _ => apply H
         end.
    all: apply (events_equiv EQ); auto. }
  { pomset_equiv_rewrite. now rewrite (write_κ HH), EQ. }
  { pomset_equiv_rewrite. apply HH. now rewrite <- EQ. }
  { assert (events_set y ≡₁ events_set x) as QQ by apply EQ.
    pomset_equiv_rewrite.
    rewrite write_pt0.
    now apply subst_q_more. }
  pomset_equiv_rewrite.
  now rewrite (write_term HH).
Qed.

Add Morphism FENCE with signature
  pomset_equiv ==> eq ==> eq ==> iff as fence_more.
Proof.
  enough (forall x y t r,
             pomset_equiv y x -> FENCE x t r -> FENCE y t r) as AA.
  { ins; desf. now split; apply AA. }
  intros x y t r EQ HH; inv HH.
  constructor; ins.
  all: try by pomset_equiv_rewrite; try apply HH.
  { by rewrite EQ. }
  { apply functional_extensionality; ins. 
    pomset_equiv_rewrite. rewrite (fence_λ HH).
    clear -EQ. desf; exfalso.
    all: match goal with
         | H : ~ events_set _ _ |- _ => apply H
         end.
    all: apply (events_equiv EQ); auto. }
  pomset_equiv_rewrite.
  rewrite (fence_term HH).
  clear -EQ. desf; try easy.
  all: exfalso; ins; desf.
  all: match goal with
       | H : ~ _ |- _ => apply H
       end.
  all: try rewrite <- (events_equiv EQ); auto.
  all: rewrite (events_equiv EQ); auto.
Qed.

Add Morphism pomset_union with signature
  pomset_equiv ==> pomset_equiv ==> pomset_equiv ==> iff as pomset_union_more.
Proof.
  enough (forall x x' y y' z z'
                 (EQX : pomset_equiv x' x)
                 (EQY : pomset_equiv y' y)
                 (EQZ : pomset_equiv z' z)
                 (HH: pomset_union x y z),
             pomset_union x' y' z') as AA.
  { ins; desf. now split; apply AA. }
  ins. inv HH.
  constructor; ins.
  all: pomset_equiv_rewrite; auto.
Qed.

Add Morphism label_union with signature
  pomset_equiv ==> pomset_equiv ==> pomset_equiv ==> iff as label_union_more.
Proof.
  enough (forall x x' y y' z z'
                 (EQX : pomset_equiv x' x)
                 (EQY : pomset_equiv y' y)
                 (EQZ : pomset_equiv z' z)
                 (HH: label_union x y z),
             label_union x' y' z') as AA.
  { ins; desf. now split; apply AA. }
  ins.
  red. red in HH.
  ins. pomset_equiv_rewrite; auto.
  symmetry in EQY. symmetry in EQZ.
  ins. split; intros AA; apply HH.
  all: eapply events_equiv; eauto.
Qed.

Lemma seq_κ_def_more x x' y y' r r' f f' e
      (* this requirement is the reason why the lemma is not defined as a morphism *)
      (WFX : wf x) 

      (EQX : pomset_equiv x' x)
      (EQY : pomset_equiv y' y)
      (EQR : r' ≡ r)
      (EQF : func_equiv f f') : 
  seq_κ_def x y f r e ⇔ seq_κ_def x' y' f' r' e.
Proof.
  enough (forall x x' y y' r r' f f' e
                 (WFX : wf x) 
                 (EQX : pomset_equiv x' x)
                 (EQY : pomset_equiv y' y)
                 (EQR : r' ≡ r)
                 (EQF : func_equiv f f'),
                 Formula.entails (seq_κ_def x y f r e) (seq_κ_def x' y' f' r' e)) as AA.
  { split; apply AA; auto; try easy.
    now rewrite EQX. }
  clear. ins. unfold seq_κ_def. desf.
  all: try by exfalso; match goal with
                       | H : ~ events_set _ ?X,
                         N :   events_set _ ?X |- _ =>
                         now apply H; eapply events_equiv; eauto
                       end.
  all: try by exfalso; match goal with
                       | H : ~ is_r' _ ,
                         N :   is_r' _  |- _ =>
                           by rewrite EQF in H; desf
                       | H : ~ is_r' _ ,
                         N :   is_r' _  |- _ =>
                           by rewrite EQF in N; desf
                       end.
  all: pomset_equiv_rewrite; try easy.
  all: try by apply entails_left_disj.
  all: try apply entails_resp_disj; try easy.

  all: etransitivity; [|eapply wf_pt_family; auto];
    [eapply pt_entails; [by apply WFX|];
     pomset_equiv_rewrite; easy|].
  all: try (rewrite (events_equiv EQX); basic_solver).
  all: rewrite EQR; basic_solver 10.
Qed.

Add Morphism SEQ with signature
  pomset_equiv ==> pomset_equiv ==> pomset_equiv ==> iff as seq_more.
Proof.
  enough (forall x x' y y' z z'
                 (EQX : pomset_equiv x' x)
                 (EQY : pomset_equiv y' y)
                 (EQZ : pomset_equiv z' z)
                 (HH: SEQ x y z),
             SEQ x' y' z') as AA.
  { ins; desf. now split; apply AA; auto. }
  ins. inv HH.
  assert (wf y) as WFY by apply HH.

  constructor; ins.
  all: pomset_equiv_rewrite.
  all: try by rewrite EQX.
  all: try by rewrite EQY.
  1,2: by rewrite EQX, EQY, EQZ; apply HH.
  { rewrite (seq_κ HH).
    eapply seq_κ_def_more; auto; pomset_equiv_rewrite; try easy.
    apply func_equiv_symmetric. apply EQX. }
  { rewrite (seq_pt HH).
    apply pt_more; [by apply WFY|].
    now pomset_equiv_rewrite. }
  { rewrite (seq_term HH).
    arewrite (τ y (events_set y) (term z) ⇔ τ y (events_set y') (term z')).
    2: easy.
    erewrite wf_pt_family_equiv; try apply WFY.
    2: by symmetry; apply EQY.
    apply pt_more; [by apply WFY|].
    now pomset_equiv_rewrite. }
  { enough ((sync x)^? d e) as [|AA]; subst; eauto.
    { right. now apply EQX. }
    apply EQY in E1D. apply EQZ in E2D.
    rewrite (labels_equiv EQY) in SYNC.
    rewrite (labels_equiv EQZ) in SYNC.
    now apply HH. }
  enough ((perloc x)^? d e) as [|AA]; subst; eauto.
  { right. now apply EQX. }
  apply EQY in E1D. apply EQZ in E2D.
  rewrite (labels_equiv EQY) in COH.
  rewrite (labels_equiv EQZ) in COH.
  now apply HH.
Qed.

Add Morphism if_κ_def with signature
  pomset_equiv ==> pomset_equiv ==> eq ==> eq ==> Formula.equiv as if_κ_def_more.
Proof.
  enough (forall x x' y y' φ e
                 (EQX : pomset_equiv x' x)
                 (EQY : pomset_equiv y' y),
             Formula.entails (if_κ_def x y φ e) (if_κ_def x' y' φ e)) as AA.
  { ins; desf. now split; apply AA. }
  clear. ins. unfold if_κ_def. desf.
  all: pomset_equiv_rewrite; try easy.
  all: exfalso; match goal with
                | H : ~ events_set _ ?X,
                  N :   events_set _ ?X |- _ =>
                  now apply H; eapply events_equiv; eauto
                | H : ~ events_set _ ?X,
                  N :   events_set _ ?X |- _ =>
                  apply H; eapply events_equiv;
                    (try by (symmetry; eauto));
                    auto
                end.
Qed.

Add Morphism IFF with signature
  pomset_equiv ==> pomset_equiv ==> pomset_equiv ==> eq ==> iff as if_more.
Proof.
  enough (forall x x' y y' z z' ψ
                 (EQX : pomset_equiv x' x)
                 (EQY : pomset_equiv y' y)
                 (EQZ : pomset_equiv z' z)
                 (HH : IFF x y z ψ),
             IFF x' y' z' ψ) as AA.
  { ins; desf. now split; apply AA. }
  ins. inv HH.
  constructor; ins.
  all: pomset_equiv_rewrite.
  all: try by rewrite EQX.
  1,2: by rewrite EQX, EQY, EQZ; apply HH.
  { rewrite (if_κ HH). now rewrite EQY, EQZ. }
  now rewrite (if_term HH).
Qed.

Add Morphism Semantics with signature
  eq ==> eq ==> pomset_equiv ==> iff as semantics_more.
Proof.
  intros t sx P1 P2 EQ.
  enough (forall P1 P2 (EQ : pomset_equiv P2 P1)
                 (HH : Semantics t sx P1),
             Semantics t sx P2) as AA.
  { now split; apply AA. }
  clear P1 P2 EQ.
  induction sx; ins.
  1-5: by inv HH; econstructor; eauto; rewrite EQ; eauto.
  { inv HH. eapply interp_if with (P1:=P0); eauto. by rewrite EQ. }
  inv HH. eapply interp_seq; eauto. by rewrite EQ.
Qed.
