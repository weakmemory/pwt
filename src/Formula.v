From hahn Require Import Hahn.
From imm Require Import Events.
From imm Require Import Prog.

Require Import Language.
Require Import Events.
Require Import Btauto.
Require Import Bool Ring.
Require Import AuxDef.
Require Import Lia.

Import ListNotations.

Module Formula.

Inductive t :=
  (* formulae include equalities (𝑀=𝑁) and (𝑥=𝑀) *)
| eqEE (m n : Expr.t)
| eqLE (x : location)  (m : Expr.t)
| q (x : location)
  (* formulae are closed under negation, conjunction, disjunction, and
     substitutions [𝑀/𝑟], [𝑀/𝑥] *)
| neg  (φ : t)
| disj (φ ψ : t)
| ff.

Definition tt := neg ff.

Definition disj_list (l : list t) := fold_right disj ff l.

Definition conj (φ ψ : t) := neg (disj (neg φ) (neg ψ)).
Definition conj_list (l : list t) := fold_right conj tt l.

Definition impl (φ ψ : t) := disj (neg φ) ψ.

Fixpoint eval
         (locf  : location -> value)
         (regf  : Reg.t -> value)
         (eregf : Event.t -> value)
         (qf    : location -> bool)
         φ : bool :=
  match φ with
  | eqEE m n => Nat.eqb
                   (Expr.eval regf eregf m)
                   (Expr.eval regf eregf n)
  | eqLE l m => Nat.eqb (locf l) (Expr.eval regf eregf m)
  | neg  φ   => negb (eval locf regf eregf qf φ)
  | disj φ ψ => (eval locf regf eregf qf φ) || (eval locf regf eregf qf ψ)
  | q    l   => qf l
  | ff       => false
  end.

Definition entails φ ψ :=
  forall locf regf eregf qf,
    implb (eval locf regf eregf qf φ)
          (eval locf regf eregf qf ψ).

Definition tautology φ := entails tt φ.

Definition satisfiable (φ : t) := ~ (entails φ ff).

Definition equiv (φ ψ : t) := (entails φ ψ) /\ (entails ψ φ).

Module Import Syntax.

Declare Scope formula_scope.

Notation "φ ∨ ψ" := (disj φ ψ)
                      (at level 15, right associativity) : formula_scope.
Notation "¬ φ" := (neg φ)
                    (at level 13) : formula_scope.
Notation "φ ∧ ψ" := (conj φ ψ)
                      (at level 14, right associativity) : formula_scope.
Notation "φ ⇒ ψ" := (impl φ ψ)
                      (at level 15, right associativity) : formula_scope.
Notation "φ ⊨ ψ" := (entails φ ψ)
                      (at level 80) : formula_scope.
Notation "φ ⇔ ψ" := (equiv φ ψ)
                      (at level 16, right associativity) : formula_scope.

End Syntax.

(****************************)
(* SUBSTITUTION DEFINITIONS *)
(****************************)

Fixpoint subst_loc (φ : t) (x : location)  (m : Expr.t) : t :=
  match φ with
  | eqEE e1 e2 => eqEE e1 e2
  | eqLE x' e => if Loc.Loc.eqb x x' then eqEE m e else  eqLE x' e
  | neg φ' => neg (subst_loc φ' x m)
  | disj φ' ψ' => disj (subst_loc φ' x m) (subst_loc ψ' x m)
  | _ => φ
  end.

Fixpoint subst_reg (φ : t) (x : Reg.t)  (m : Expr.t) : t :=
  match φ with
  | eqEE e1 e2 => eqEE (Expr.subst_reg e1 x m) (Expr.subst_reg e2 x m)
  | eqLE x' e => eqLE x' (Expr.subst_reg e x m)
  | neg φ' => neg (subst_reg φ' x m)
  | disj φ' ψ' => disj (subst_reg φ' x m) (subst_reg ψ' x m)
  | _ => φ
  end.

Fixpoint subst_q (φ : t) (x : location) (ψ : t) : t :=
  match φ with
  | eqEE e1 e2 => φ
  | eqLE x' e => φ
  | neg φ' => neg (subst_q φ' x ψ)
  | disj φ' ψ' => disj (subst_q φ' x ψ) (subst_q ψ' x ψ)
  | q x' => ifP x' = x
            then ψ
            else φ
  | _ => φ
  end.

Fixpoint subst_ereg_val (φ : t) (e : Event.t)  (v : value) : t :=
  match φ with
  | eqEE e1 e2 => eqEE (Expr.subst_ereg e1 e (Expr.val v))
                       (Expr.subst_ereg e2 e (Expr.val v))
  | eqLE x' e' => eqLE x' (Expr.subst_ereg e' e (Expr.val v))
  | neg φ' => neg (subst_ereg_val φ' e v)
  | disj φ' ψ' => disj (subst_ereg_val φ' e v) (subst_ereg_val ψ' e v)
  | _ => φ
  end.

Definition subst_ereg_val_list
           (φ : t)
           (l : list (Event.t * value)) : t :=
  List.fold_right (fun ev ψ => subst_ereg_val ψ (fst ev) (snd ev)) φ l.

Fixpoint used_exprs (φ : t) : list Expr.t :=
  match φ with
  | eqEE m n => [m; n]
  | eqLE l m => [m]
  | neg  φ   => used_exprs φ
  | disj φ ψ => used_exprs φ ++ used_exprs ψ
  | _        => nil
  end.

(**********************)
(* USED_X DEFINITIONS *)
(**********************)

Fixpoint used_regs (φ : t) : list Reg.t :=
  match φ with
  | eqEE m n => Expr.used_regs m ++ Expr.used_regs n
  | eqLE l m => Expr.used_regs m
  | neg  φ   => used_regs φ
  | disj φ ψ => used_regs φ ++ used_regs ψ
  | _        => nil
  end.

Fixpoint used_eregs (φ : t) : list Event.t :=
  match φ with
  | eqEE m n => Expr.used_eregs m ++ Expr.used_eregs n
  | eqLE l m => Expr.used_eregs m
  | neg  φ   => used_eregs φ
  | disj φ ψ => used_eregs φ ++ used_eregs ψ
  | _        => nil
  end.

Fixpoint used_locs (φ : t) : list location :=
  match φ with
  | eqEE m n => nil
  | eqLE l m => [l]
  | neg  φ   => used_locs φ
  | disj φ ψ => used_locs φ ++ used_locs ψ
  | _        => nil
  end.

Fixpoint used_q (φ : t) : list location :=
  match φ with
  | q l      => [l]
  | neg  φ   => used_q φ
  | disj φ ψ => used_q φ ++ used_q ψ
  | _        => nil
  end.

Definition deps_set {A} (df : RegFun.t (A -> Prop)) φ e :=
  exists r,
    << UREG : List.In r (used_regs φ) >> /\
    << INDEPF : df r e >>.

Definition deps_set_alt {A} (df : RegFun.t (A -> Prop)) φ e :=
  exists m,
    << UEXPR      : List.In m (used_exprs φ) >> /\
    << INDEPSEXPR : Expr.deps_set df m e >>.

Module Properties.

Open Scope formula_scope.

(*********************)
(* USED_X_PROPERTIES *)
(*********************)

Lemma used_regs_subst_reg φ r m :
  lset (used_regs (subst_reg φ r m)) ≡₁
  lset (used_regs φ) \₁ eq r ∪₁
  codom_rel ((lset (used_regs φ) ∩₁ eq r) × lset (Expr.used_regs m)).
Proof.
  induction φ; auto; simpls.
  { rewrite !lset_app.
    erewrite !Expr.used_regs_subst_reg; eauto.
    basic_solver 10. }
  { erewrite !Expr.used_regs_subst_reg; eauto. }
  { basic_solver. }
  { rewrite !lset_app.
    rewrite IHφ1, IHφ2.
    basic_solver 10. }
  basic_solver.
Qed.

Lemma used_eregs_subst_reg φ r m :
  lset (used_eregs (subst_reg φ r m)) ≡₁
  lset (used_eregs φ) ∪₁
  ifP (lset (used_regs φ) r) then lset (Expr.used_eregs m) else ∅.
Proof.
  induction φ; auto; simpls.
  { desf.
    { rewrite !lset_app.
      apply lset_app in l.
      erewrite !Expr.used_eregs_subst_reg; eauto.
      desf; try basic_solver 20.
      inv l; basic_solver. }
    rewrite !lset_app.
    assert (~ lset (Expr.used_regs m0) r) as NM0.
    { intro; apply n0, lset_app; basic_solver 20. }
    assert (~ lset (Expr.used_regs n) r) as NN.
    { intro; apply n0, lset_app; basic_solver 20. }
    rewrite !Expr.used_eregs_subst_reg; eauto.
    desf; try basic_solver 20. }
  { rewrite !Expr.used_eregs_subst_reg; eauto. }
  { basic_solver. }
  { rewrite !lset_app, IHφ1, IHφ2.
    desf.
    1,3,5,8: basic_solver.
    all: exfalso.
    { apply n, lset_app. basic_solver. }
    { apply n0, lset_app. basic_solver. }
    { apply n0, lset_app. basic_solver. }
    apply lset_app in l. inv l. }
  basic_solver.
Qed.

Lemma used_locs_subst_reg φ r m :
  used_locs (subst_reg φ r m) = used_locs φ.
Proof.
  induction φ; simpls; auto.
  by rewrite IHφ1, IHφ2.
Qed.

Lemma used_q_subst_q φ l ψ:
  lset (used_q (subst_q φ l ψ)) ≡₁
       lset (used_q φ) \₁ (eq l) ∪₁
       dom_rel (lset (used_q ψ) × (lset (used_q φ) ∩₁ eq l)).
Proof.
  induction φ; desf; ins.
  4: rewrite !lset_app, IHφ1, IHφ2; basic_solver 10.
  all: desf; basic_solver 10.
Qed.

Lemma used_q_subst_reg φ l m:
  used_q (subst_reg φ l m) = used_q φ.
Proof.
  induction φ; simpls; auto.
  by rewrite IHφ1, IHφ2.
Qed.

Lemma used_locs_disj_list l :
  used_locs (disj_list l) = concat (map used_locs l).
Proof.
  induction l; ins; desf.
  by rewrite IHl.
Qed.

Lemma used_eregs_disj_list l :
  used_eregs (disj_list l) = concat (map used_eregs l).
Proof.
  induction l; ins; desf.
  by rewrite IHl.
Qed.

Lemma used_regs_disj_list l :
  used_regs (disj_list l) = concat (map used_regs l).
Proof.
  induction l; ins; desf.
  by rewrite IHl.
Qed.

Lemma used_q_disj_list l :
  used_q (disj_list l) = concat (map used_q l).
Proof.
  induction l; ins; desf.
  by rewrite IHl.
Qed.

(*******************)
(* NO_X PROPERTIES *)
(*******************)

Lemma nin_subst_reg φ r m
      (NO_REG : ~ (lset (used_regs φ)) r) :
  subst_reg φ r m = φ.
Proof.
  induction φ; auto; simpls.
  { rewrite !Expr.nin_subst_reg; auto.
    all: intro; apply NO_REG, lset_app; basic_solver. }
  { by rewrite Expr.nin_subst_reg. }
  { by rewrite IHφ. }
  rewrite IHφ1, IHφ2; auto.
  all: intro; apply NO_REG, lset_app; basic_solver.
Qed.

Lemma nin_subst_ereg_val φ e v
      (NO_EREG : ~ (lset (used_eregs φ)) e) :
  subst_ereg_val φ e v = φ.
Proof.
  induction φ; auto; simpls.
  { rewrite !Expr.nin_subst_ereg; auto.
    all: intro; apply NO_EREG, lset_app; basic_solver. }
  { by rewrite Expr.nin_subst_ereg. }
  { by rewrite IHφ. }
  rewrite IHφ1, IHφ2; auto.
  all: intro; apply NO_EREG, lset_app; basic_solver.
Qed.

Lemma nin_subst_ereg_val_list φ l
      (NO_EREG : set_disjoint
                  (lset (used_eregs φ))
                  (lset (map fst l))) :
  subst_ereg_val_list φ l = φ.
Proof.
  induction l; ins; desf.
  rewrite lset_cons in NO_EREG.
  apply set_disjoint_union_r in NO_EREG; desf.
  apply set_disjoint_eq_r in NO_EREG.
  rewrite IHl; auto.
  rewrite nin_subst_ereg_val; auto.
Qed.

Lemma no_loc_subst_loc φ l m
      (NO_LOC : ~ (lset (used_locs φ)) l) :
  subst_loc φ l m = φ.
Proof.
  induction φ; auto; simpls; clarify_not.
  { desf; basic_solver. }
  { rewrite IHφ; auto. }
  rewrite IHφ1, IHφ2; auto.
  all: intro; apply NO_LOC, lset_app; basic_solver.
Qed.

Lemma no_q_subst_q φ l ψ
      (NO_Q : ~ (lset (used_q φ)) l) :
  subst_q φ l ψ = φ.
Proof.
  induction φ; auto; simpls; clarify_not.
  { desf; basic_solver. }
  { rewrite IHφ; auto. }
  rewrite IHφ1, IHφ2; auto.
  all: intro; apply NO_Q, lset_app; try basic_solver.
Qed.

(**********************)
(* SUBST_X PROPERTIES *)
(**********************)

Lemma compose_subst_ereg_val_subst_reg φ r e v :
  subst_ereg_val (subst_reg φ r (Expr.ereg e)) e v
  =
  subst_reg (subst_ereg_val φ e v) r (Expr.val v).
Proof.
  induction φ; simpls; auto.
  { rewrite !Expr.compose_subst_ereg_subst_reg; auto.
    all: intro HH; apply NO_EREG, lset_app; basic_solver. }
  { rewrite !Expr.compose_subst_ereg_subst_reg; auto. }
  { by rewrite IHφ. }
  rewrite IHφ1, IHφ2; auto.
Qed.

Lemma compose_subst_ereg_val_subst_reg_noereg φ r e v
      (NO_EREG : ~ (lset (used_eregs φ)) e) :
  subst_ereg_val (subst_reg φ r (Expr.ereg e)) e v
  =
  subst_reg φ r (Expr.val v).
Proof.
  by rewrite compose_subst_ereg_val_subst_reg, nin_subst_ereg_val.
Qed.

Lemma subst_ereg_val_list_alt φ l :
  let alt_def :=
      match φ with
      | eqEE m n => eqEE (Expr.subst_ereg_val_list m l) (Expr.subst_ereg_val_list n l)
      | eqLE x m => eqLE x (Expr.subst_ereg_val_list m l)
      | q x      => q x
      | neg φ    => neg (subst_ereg_val_list φ l)
      | disj φ ψ => disj (subst_ereg_val_list φ l) (subst_ereg_val_list  ψ l)
      | ff       => ff
      end
  in subst_ereg_val_list φ l = alt_def.
Proof.
  induction l; desf; ins; rewrite ?IHl; ins.
Qed.

Lemma subst_ereg_val_list_conj φ ψ l :
  subst_ereg_val_list (φ ∧ ψ) l = subst_ereg_val_list φ l ∧ subst_ereg_val_list ψ l.
Proof.
  repeat (rewrite subst_ereg_val_list_alt; ins).
Qed.

Lemma subst_ereg_val_list_impl φ ψ l :
  subst_ereg_val_list (φ ⇒ ψ) l = subst_ereg_val_list φ l ⇒ subst_ereg_val_list ψ l.
Proof.
  repeat (rewrite subst_ereg_val_list_alt; ins).
Qed.

Lemma subst_ereg_val_conj_list l e v:
  subst_ereg_val (conj_list l) e v
  =
  conj_list (map (fun φ => subst_ereg_val φ e v) l).
Proof.
  induction l; desf; ins.
  by rewrite IHl.
Qed.

Lemma subst_ereg_val_list_conj_list l_φ l_ev:
  subst_ereg_val_list (conj_list l_φ) l_ev
  =
  conj_list (map (fun φ => subst_ereg_val_list φ l_ev) l_φ).
Proof.
  induction l_ev; desf; ins.
  { by rewrite map_id. }
  by rewrite IHl_ev, subst_ereg_val_conj_list, map_map.
Qed.

Lemma subst_ereg_val_subst_loc_commute φ l m e v
      (NOEREG : ~ lset (Expr.used_eregs m) e) :
  subst_ereg_val (subst_loc φ l m) e v =
  subst_loc (subst_ereg_val φ e v) l m.
Proof.
  induction φ; auto; simpls.
  { desf; simpl; [| basic_solver].
    induction m; simpls.
    clarify_not.
    desf; basic_solver. }
  { by rewrite IHφ. }
  by rewrite IHφ1, IHφ2.
Qed.

Lemma subst_ereg_val_subst_reg_commute φ r m e v
      (NOEREG : ~ lset (Expr.used_eregs m) e) :
  subst_ereg_val (subst_reg φ r m) e v =
  subst_reg (subst_ereg_val φ e v) r m.
Proof.
  induction φ; auto; simpls.
  1-2: by rewrite !Expr.subst_ereg_val_subst_reg_commute; auto.
  { by rewrite IHφ. }
  by rewrite IHφ1, IHφ2.
Qed.

Lemma subst_ereg_val_list_subst_reg_commute φ r m l
      (NOEREG : set_disjoint
                  (lset (Expr.used_eregs m))
                  (lset (map fst l))) :
  subst_ereg_val_list (subst_reg φ r m) l =
  subst_reg (subst_ereg_val_list φ l) r m.
Proof.
  induction l; auto.
  rewrite map_cons, lset_cons in NOEREG.
  apply set_disjoint_union_r in NOEREG.
  simpls.
  rewrite <- subst_ereg_val_subst_reg_commute, IHl; basic_solver.
Qed.

Lemma subst_ereg_val_list_subst_loc_commute φ r m l
      (NOEREG : set_disjoint
                  (lset (Expr.used_eregs m))
                  (lset (map fst l))) :
  subst_ereg_val_list (subst_loc φ r m) l =
  subst_loc (subst_ereg_val_list φ l) r m.
Proof.
  induction l; auto.
  rewrite map_cons, lset_cons in NOEREG.
  apply set_disjoint_union_r in NOEREG.
  simpls.
  rewrite <- subst_ereg_val_subst_loc_commute, IHl; basic_solver.
Qed.

Lemma subst_ereg_val_no_ereg φ e v :
  ~ lset (used_eregs (subst_ereg_val φ e v)) e.
Proof.
  induction φ; auto; simpls.
  { intro LSET.
    apply lset_app in LSET.
    destruct LSET; eapply Expr.subst_ereg_no_ereg; eauto. }
  { eapply Expr.subst_ereg_no_ereg; eauto. }
  intro LSET.
  apply lset_app in LSET.
  destruct LSET; auto.
Qed.

Lemma subst_ereg_val_idemp φ e v v' :
  subst_ereg_val (subst_ereg_val φ e v) e v' =
  subst_ereg_val φ e v.
Proof.
  induction φ; auto; simpls.
  1,2:  by rewrite !Expr.subst_ereg_val_idemp.
  { rewrite IHφ; auto. }
  rewrite IHφ1, IHφ2; auto.
Qed.

Lemma subst_ereg_val_list_same_ev φ l ev
      (NEMPTY  : In ev l)
      (SAME_EV : forall ev' (IN : In ev' l), (ev' = ev)) :
  subst_ereg_val_list φ l = subst_ereg_val φ (fst ev) (snd ev).
Proof.
  induction l.
  { basic_solver. }
  assert (a = ev).
  { apply SAME_EV. basic_solver. }
  subst.
  destruct l.
  simpl.
  { basic_solver. }
  remember (p :: l) as l'.
  simpls.
  assert (p = ev).
  { apply SAME_EV. right. basic_solver. }
  subst.
  rewrite IHl.
  rewrite subst_ereg_val_idemp; auto.
  all: basic_solver.
Qed.

Lemma subst_ereg_val_list_app φ l1 l2 :
  subst_ereg_val_list φ (l1 ++ l2) =
  subst_ereg_val_list (subst_ereg_val_list φ l2) l1.
Proof.
  unfold subst_ereg_val_list.
  by rewrite fold_right_app.
Qed.

Lemma subst_neq_ereg_val_commute φ e v e' v'
      (NEQ : ~ e = e') :
  subst_ereg_val (subst_ereg_val φ e v) e' v' =
  subst_ereg_val (subst_ereg_val φ e' v') e v.
Proof.
  induction φ; simpls; auto.
  { by rewrite !Expr.subst_neq_ereg_val_commute with (e := e) (v := v). }
  { by rewrite !Expr.subst_neq_ereg_val_commute with (e := e) (v := v). }
  { by rewrite IHφ. }
  by rewrite IHφ1, IHφ2.
Qed.

Lemma subst_ereg_val_list_perm φ l l'
      (UNIQe : NoDup (map fst l))
      (PERM : Permutation l l') :
  subst_ereg_val_list φ l = subst_ereg_val_list φ l'.
Proof.
  set (P (l l' : list (Event.t * value)) :=
         forall φ
           (UNIQe : NoDup (map fst l)),
           subst_ereg_val_list φ l = subst_ereg_val_list φ l').
  generalize dependent UNIQe.
  generalize dependent φ.
  apply Permutation_ind_transp with (P := P).
  1,4 : basic_solver.
  { subst P; ins.
    rewrite !subst_ereg_val_list_app; ins.
    rewrite subst_neq_ereg_val_commute; auto.
    rewrite map_app in UNIQe.
    apply nodup_append_right, nodup_cons in UNIQe.
    basic_solver. }
  subst P; ins.
  etransitivity; [by apply H0 |]. eapply H2.
  eapply Permutation_NoDup; [| by apply UNIQe].
  apply Permutation_map; auto.
Qed.

Lemma subst_ereg_val_noereg e φ e' v'
      (NO_EREG :  ~ lset (used_eregs φ) e) :
  ~ lset (used_eregs (subst_ereg_val φ e' v')) e.
Proof.
  induction φ; ins; auto.
  { intro HH; apply lset_app in HH.
    destruct HH as [QQ | QQ]; apply NO_EREG, lset_app; [left | right].
    all: apply NNPP; intro; eapply Expr.subst_ereg_val_noereg; basic_solver. }
  { by apply Expr.subst_ereg_val_noereg. }
  intro HH; apply lset_app in HH; destruct HH.
  1: apply IHφ1; auto.
  2: apply IHφ2; auto.
  all: intro QQ; apply NO_EREG, lset_app; basic_solver.
Qed.

Lemma subst_ereg_val_list_noereg e φ l
      (NO_EREG :  ~ lset (used_eregs φ) e) :
  ~ lset (used_eregs (subst_ereg_val_list φ l)) e.
Proof.
  induction l; ins; auto.
  apply subst_ereg_val_noereg; auto.
Qed.

Lemma subst_ereg_val_list_undup φ l :
  subst_ereg_val_list φ (undup l) = subst_ereg_val_list φ l.
Proof.
  induction l; simpl; desf; ins.
  2: { by rewrite IHl. }
  rewrite IHl.
  symmetry.
  apply nin_subst_ereg_val.
  apply in_split in i; desf.
  rewrite subst_ereg_val_list_app; ins.
  apply subst_ereg_val_list_noereg, subst_ereg_val_no_ereg.
Qed.

Lemma subst_ereg_val_list_eqv_func_lists φ l l'
      (FUNC_l  : func_list l)
      (EQV     : lset l ≡₁ lset l') :
  subst_ereg_val_list φ l = subst_ereg_val_list φ l'.
Proof.
  etransitivity; [| by apply subst_ereg_val_list_undup].
  etransitivity; [by symmetry; apply subst_ereg_val_list_undup |].
  apply subst_ereg_val_list_perm.
  2: { apply NoDup_Permutation.
       1-2: by apply nodup_undup.
       ins.
       etransitivity; [by apply in_undup_iff |].
       etransitivity; [| by symmetry; apply in_undup_iff].
       split; ins; apply EQV; basic_solver. }
  apply nodup_map.
  { apply nodup_undup. }
  intros ev ev' IN IN' NEQ NEQ_FST.
  apply NEQ, FUNC_l; eauto.
 all: by apply in_undup_iff.
Qed.

Lemma subst_ereg_val_list_subst_ereg_val_commute φ e v l
      (DISJ : forall p (IN : In p l), fst p <> e) :
  subst_ereg_val_list (subst_ereg_val φ e v) l =
  subst_ereg_val (subst_ereg_val_list φ l) e v.
Proof.
  induction l; auto; ins.
  rewrite IHl.
  { apply subst_neq_ereg_val_commute.
    intros AA. eapply DISJ; eauto. }
  ins; apply DISJ; auto.
Qed.

Lemma subst_q_subst_loc_commute φ xl m xq ψ
      (NO_LOC : ~ (lset (used_locs ψ)) xl) :
  subst_q (subst_loc φ xl m) xq ψ =
  subst_loc (subst_q φ xq ψ) xl m.
Proof.
  induction φ; ins; desf.
  1,2: basic_solver.
  { rewrite no_loc_subst_loc; auto. }
  { rewrite IHφ; auto. }
  rewrite IHφ1, IHφ2; auto.
Qed.

Lemma subst_ereg_val_subst_q_commute φ xq ψ e v
      (NOEREG : ~ lset (used_eregs ψ) e) :
  subst_ereg_val (subst_q φ xq ψ) e v =
  subst_q (subst_ereg_val φ e v) xq ψ.
Proof.
  induction φ; ins; desf.
  { apply nin_subst_ereg_val; auto. }
  { rewrite IHφ; auto. }
  rewrite IHφ1, IHφ2; auto.
Qed.

Lemma subst_ereg_val_list_subst_q_commute φ xq ψ l
      (NOEREG : set_disjoint
                  (lset (used_eregs ψ))
                  (lset (map fst l))) :
  subst_ereg_val_list (subst_q φ xq ψ) l =
  subst_q (subst_ereg_val_list φ l) xq ψ.
Proof.
  induction l; ins; desf.
  rewrite lset_cons, set_disjoint_union_r in NOEREG; desf.
  apply set_disjoint_eq_r in NOEREG.
  rewrite IHl, subst_ereg_val_subst_q_commute; auto.
Qed.

Lemma subst_reg_same_reg φ r :
  subst_reg φ r (Expr.reg r) = φ.
Proof.
  induction φ; ins; desf.
  all: rewrite ?Expr.subst_reg_same_reg; congruence.
Qed.


(*******************)
(* EVAL PROPERTIES *)
(*******************)

Lemma eval_subst_reg locf regf eregf qf φ x m :
  let regf' := fun y =>
                 if BinPos.Pos.eqb x y
                 then Expr.eval regf eregf m
                 else regf y
  in eval locf regf  eregf qf (subst_reg φ x m) =
     eval locf regf' eregf qf φ.
Proof.
  induction φ; simpls.
  { by rewrite !Expr.eval_subst_reg. }
  { by rewrite !Expr.eval_subst_reg. }
  { by rewrite IHφ. }
  by rewrite IHφ1, IHφ2.
Qed.

Lemma eval_subst_loc locf regf eregf qf φ x m :
  let locf' := fun y =>
                 if BinPos.Pos.eqb x y
                 then Expr.eval regf eregf m
                 else locf y
  in eval locf  regf eregf qf (subst_loc φ x m) =
     eval locf' regf eregf qf φ.
Proof.
  induction φ; simpls.
  { by desf. }
  { by rewrite IHφ. }
  by rewrite IHφ1, IHφ2.
Qed.

Lemma eval_subst_ereg_val locf regf eregf qf φ e v :
  let eregf' := fun e' =>
                 if Event.eq e e'
                 then v
                 else eregf e'
  in eval locf regf eregf  qf (subst_ereg_val φ e v) =
     eval locf regf eregf' qf φ.
Proof.
  induction φ; simpls.
  { by rewrite !Expr.eval_subst_ereg_val. }
  { by rewrite !Expr.eval_subst_ereg_val. }
  { by rewrite IHφ. }
  by rewrite IHφ1, IHφ2.
Qed.

Lemma eval_subst_q locf regf eregf qf φ x ψ:
  let qf' := fun x' =>
               if BinPos.Pos.eqb x x'
               then eval locf regf eregf qf ψ
               else qf x'
  in eval locf regf eregf qf (subst_q φ x ψ) =
     eval locf regf eregf qf' φ.
Proof.
  induction φ; desf; ins.
  { desf; basic_solver. }
  { by rewrite IHφ. }
  by rewrite IHφ1, IHφ2.
Qed.

Ltac red_helper :=
  unfold "⇔", "⊨", implb; simpls; unfold negb, "||".

Lemma eval_subst_loc_new_reg φ l r locf regf eregf qf
      (NO_REG : ~ (lset (used_regs φ)) r) :
  let regf' x := if Reg.eqb x r then locf l else regf x
  in eval locf regf  eregf qf φ =
     eval locf regf' eregf qf (subst_loc φ l (Expr.reg r)).
Proof.
  induction φ; auto; simpls.
  { induction m; induction n;
      simpls; clarify_not; unfold RegFun.find; basic_solver. }
  { desf; simpls.
    all:
      by unfold RegFun.find; desf; simpls;
      induction m; simpls; unfold RegFun.find;
      clarify_not; desf. }
  { by rewrite IHφ. }
  rewrite IHφ1, IHφ2; auto.
  all: intro; apply NO_REG, lset_app; basic_solver.
Qed.

(*************************)
(* ENTAILMENT PROPERTIES *)
(*************************)

Lemma entails_refl φ : φ ⊨ φ.
Proof.
  red_helper.
  ins. desf.
Qed.

Lemma entails_trans : forall φ ψ χ, (φ ⊨ ψ) -> (ψ ⊨ χ) -> (φ ⊨ χ).
Proof.
  red_helper.
  intros a b c AA BB p q r qf.
  specialize (AA p q r qf); specialize (BB p q r qf).
  desf.
Qed.

Lemma entails_resp_disj : forall φ ψ ξ ζ, (φ ⊨ ψ) -> (ξ ⊨ ζ) -> ((φ ∨ ξ) ⊨ (ψ ∨ ζ)).
Proof.
  red_helper.
  intros a b c d AA BB p q r qf.
  specialize (AA p q r qf); specialize (BB p q r qf).
  desf.
Qed.

Lemma enatils_resp_conj : forall φ ψ ξ ζ, (φ ⊨ ψ) -> (ξ ⊨ ζ) -> ((φ ∧ ξ) ⊨ (ψ ∧ ζ)).
Proof.
  red_helper.
  intros a b c d AA BB p q r qf.
  specialize (AA p q r qf); specialize (BB p q r qf).
  desf.
Qed.

Lemma entails_left_disj  : forall φ ψ, φ ⊨ (φ ∨ ψ).
Proof.
  red_helper.
  ins; desf.
Qed.

Lemma entails_right_disj : forall φ ψ, ψ ⊨ (φ ∨ ψ).
Proof.
  red_helper.
  ins; desf.
Qed.

Lemma entails_elim_disj : forall φ ψ χ, (φ ⊨ χ) -> (ψ ⊨ χ) -> ((φ ∨ ψ) ⊨ χ).
Proof.
  red_helper.
  intros a b c AA BB p q r qf.
  specialize (AA p q r qf); specialize (BB p q r qf).
  desf.
Qed.

Lemma entails_resp_neg : forall φ ψ (HH : φ ⊨ ψ), (¬ ψ) ⊨ (¬ φ).
Proof.
  red_helper; ins. specialize (HH locf regf eregf qf); desf.
Qed.

Lemma entails_elim_dneg : forall φ, ¬(¬ φ) ⊨ φ.
Proof.
  red_helper.
  ins; desf.
Qed.

Lemma entails_intro_dneg : forall φ, φ ⊨ ¬(¬ φ).
Proof.
  red_helper.
  ins; desf.
Qed.

Lemma entails_elim_ff : forall φ, ff ⊨ φ.
Proof.
  red_helper.
Qed.

Lemma entails_resp_subst_loc : forall x m φ ψ,
    φ ⊨ ψ -> subst_loc φ x m ⊨ subst_loc ψ x m.
Proof.
  intros x m a b ab.
  red; ins.
  erewrite !eval_subst_loc.
  apply ab.
Qed.

Lemma entails_resp_subst_reg : forall x m φ ψ,
    φ ⊨ ψ -> subst_reg φ x m ⊨ subst_reg ψ x m.
Proof.
  intros r m a b ab.
  red; ins.
  erewrite !eval_subst_reg.
  apply ab.
Qed.

Lemma entails_resp_subst_ereg_val e v φ ψ
    (ENT : φ ⊨ ψ) :
      subst_ereg_val φ e v ⊨ subst_ereg_val ψ e v.
Proof.
  red. ins.
  erewrite !eval_subst_ereg_val.
  basic_solver.
Qed.

Lemma neqEE_entails : forall e v v',
    (v <> v') -> eqEE e (Expr.val v)
               ⊨
             ¬(eqEE e (Expr.val v')).
Proof.
  red_helper.
  ins. desf; auto; basic_solver.
Qed.

Lemma eqEE_sym : forall e1 e2,
    eqEE e1 e2 ⊨ eqEE e2 e1.
Proof.
  red_helper.
  ins; desf; auto.
  rewrite Heq.
  apply PeanoNat.Nat.eqb_refl.
Qed.

Lemma formula_lem : forall φ, tt ⊨ φ ∨ ¬φ.
Proof.
  red_helper.
  ins; desf.
Qed.
(*****************************************)
(* ENTAILMENT AND EQUIVALENCE PROPERTIES *)
(*****************************************)

Lemma entails_more_r (φ ψ ψ' : t)
      (equiv : equiv ψ ψ')
      (ent : φ ⊨ ψ) :
  φ ⊨ ψ'.
Proof.
  destruct equiv.
  eby eapply entails_trans.
Qed.

Lemma entails_more_l (φ φ' ψ : t)
      (equiv : φ ⇔ φ')
      (ent : φ ⊨ ψ) :
  φ' ⊨ ψ.
Proof.
  destruct equiv.
  eby eapply entails_trans.
Qed.

Lemma equiv_refl ψ : ψ ⇔ ψ.
Proof.
  by split; apply entails_refl.
Qed.

Lemma equiv_sym ψ ψ'
      (e : ψ ⇔ ψ') :
 ψ' ⇔ ψ.
Proof.
  by destruct e.
Qed.

Lemma equiv_trans ψ1 ψ2 ψ3
      (e1 : ψ1 ⇔ ψ2)
      (e2 : ψ2 ⇔ ψ3) :
 ψ1 ⇔ ψ3.
Proof.
  unfold "⇔" in *.
  specialize entails_trans.
  basic_solver.
Qed.

Lemma equiv_neg φ ψ
      (e : φ ⇔ ψ) :
  ¬φ ⇔ ¬ψ.
Proof.
  split; apply entails_resp_neg; inv e.
Qed.

Lemma elim_dneg φ :
  ¬(¬ φ) ⇔  φ.
Proof.
  split.
  { apply entails_elim_dneg. }
  apply entails_intro_dneg.
Qed.

Lemma entails_true φ : φ ⊨ tt.
Proof.
  eapply entails_trans; [apply entails_intro_dneg | ].
  apply entails_resp_neg, entails_elim_ff.
Qed.


Add Relation t equiv
    reflexivity proved by equiv_refl
    symmetry proved by equiv_sym
    transitivity proved by equiv_trans
      as equiv_rel.

Add Relation t entails
    reflexivity proved by entails_refl
    transitivity proved by entails_trans
      as entails_rel.

Add Morphism entails with signature
  entails --> entails ++> Basics.impl as entails_mori.
Proof.
  ins. intro.
  eapply entails_trans; eauto.
  eapply entails_trans; eauto.
Qed.

Add Morphism entails with signature
  equiv ==> equiv ==> iff as entails_more.
Proof.
  unfold equiv; split; ins; specialize entails_trans; basic_solver.
Qed.

Add Morphism equiv with signature
  equiv ==> equiv ==> iff as equiv_more.
Proof.
  specialize equiv_trans.
  specialize equiv_sym;
  split; intros; basic_solver.
Qed.

Add Morphism impl with signature
  entails --> entails ++> entails as impl_mori.
Proof.
  intros x y YX a b AB.
  unfold entails; ins.
  specialize (YX locf regf eregf qf).
  specialize (AB locf regf eregf qf).
  unfold implb, negb, orb in *.
  basic_solver.
Qed.

Add Morphism subst_reg with signature
    entails ==> eq ==> eq ==> entails as subst_reg_mori.
Proof.
  intros x y HH; ins; desf.
  red; ins.
  all: rewrite !eval_subst_reg.
  all: apply HH.
Qed.

Add Morphism subst_reg with signature
    equiv ==> eq ==> eq ==> equiv as subst_reg_more.
Proof.
  intros x y [EQ EQ']; ins; split.
  { now rewrite <- EQ. }
  now rewrite <- EQ'.
Qed.

Add Morphism subst_loc with signature
    equiv ==> eq ==> eq ==> equiv as subst_loc_more.
Proof.
  intros x y HH; ins; desf.
  split; red; ins.
  all: rewrite !eval_subst_loc.
  all: apply HH.
Qed.

Add Morphism subst_ereg_val with signature
    equiv ==> eq ==> eq ==> equiv as subst_ereg_val_more.
Proof.
  intros x y HH; ins; desf.
  split; red; ins.
  all: rewrite !eval_subst_ereg_val.
  all: apply HH.
Qed.

Add Morphism subst_ereg_val with signature
    entails ==> eq ==> eq ==> entails as subst_ereg_val_mori.
Proof.
  intros x y HH; ins; desf.
  red; ins.
  all: rewrite !eval_subst_ereg_val.
  all: apply HH.
Qed.

Add Morphism subst_ereg_val_list with signature
    equiv ==> eq ==> equiv as subst_ereg_val_list_more.
Proof.
  intros x y [xy yx] l; ins; desf.
  induction l; ins.
  rewrite IHl.
  reflexivity.
Qed.

Add Morphism subst_ereg_val_list with signature
    entails ==> eq ==> entails as subst_ereg_val_list_mori.
Proof.
  intros x y xy l; ins; desf.
  induction l; ins.
  rewrite IHl.
  reflexivity.
Qed.

(* TODO: move *)
Lemma eqb_implb a b :
  eqb a b = implb a b && implb b a.
Proof.
  unfold eqb, implb.
  basic_solver.
Qed.

Add Morphism eval with signature
    eq ==> eq ==> eq ==> eq ==> equiv ==> eq as eval_more.
Proof.
  intros locf regf eregf qf a b ab.
  red in ab.
  unfold entails in ab.
  apply eqb_prop.
  rewrite eqb_implb.
  desf.
  rewrite ab, ab0.
  done.
Qed.

(**************************)
(* DISJUNCTION PROPERTIES *)
(**************************)

Lemma disj_sym φ ψ :
  φ ∨ ψ ⇔ ψ ∨ φ.
Proof.
  split.
  all: by apply entails_elim_disj; [apply entails_right_disj | apply entails_left_disj].
Qed.

Lemma equiv_disj_idemp φ :
  φ ∨ φ ⇔ φ.
Proof.
  split.
  2: now apply entails_right_disj.
  now apply entails_elim_disj.
Qed.

Lemma entails_elim_disj_r a b c :
      (a ⊨ c /\ b ⊨ c) <-> (a ∨ b ⊨ c).
Proof.
  split; intro HH; desf.
  { by apply entails_elim_disj. }
  specialize entails_right_disj.
  specialize entails_left_disj.
  ins.
  split; etransitivity; eauto.
  eby rewrite disj_sym.
Qed.

Lemma disj_false_l x :
  ff ∨ x ⇔ x.
Proof.
  split; intro HH; unfold implb; basic_solver.
Qed.

Lemma disj_false_r x :
  x ∨ ff ⇔ x.
Proof.
  rewrite disj_sym. apply disj_false_l.
Qed.

Lemma disj_true_r x :
  x ∨ tt ⇔ tt.
Proof.
  split; intro HH; ins; unfold implb, orb; ins; basic_solver.
Qed.

Lemma disj_true_l x :
  tt ∨ x ⇔ tt.
Proof.
  rewrite disj_sym.
  apply disj_true_r.
Qed.

Lemma disjA a b c :
  (a ∨ b) ∨ c ⇔ a ∨ b ∨ c.
Proof.
  red_helper.
  splits; ins; desf.
Qed.

Add Morphism disj with signature
    Formula.entails ==> Formula.entails ==> Formula.entails as disj_mori.
Proof.
  intros x y xy a b ab.
  apply entails_resp_disj; desf.
Qed.

Add Morphism disj with signature
    Formula.equiv ==> Formula.equiv ==> Formula.equiv as disj_more.
Proof.
  unfold "⇔".
  now ins; desf; split; eapply disj_mori.
Qed.

(**************************)
(* CONJUNCTION PROPERTIES *)
(**************************)

Lemma equiv_conj_idemp φ :
  φ ⇔ φ ∧ φ.
Proof.
  unfold "∧".
  symmetry. etransitivity; [|eby apply elim_dneg].
  apply equiv_neg. apply equiv_disj_idemp.
Qed.

Lemma conj_sym φ ψ :
  φ ∧ ψ ⇔ ψ ∧ φ.
Proof.
  apply equiv_neg, disj_sym.
Qed.

Lemma conj_assoc φ ψ ξ :
  φ ∧ (ψ ∧ ξ) ⇔ (φ ∧ ψ) ∧ ξ.
Proof. red_helper; split; ins; desf. Qed.

Lemma conj_false_l x :
  ff ∧ x ⇔ ff.
Proof.
  split; intro HH; unfold implb; basic_solver.
Qed.

Lemma conj_false_r x :
  x ∧ ff ⇔ ff.
Proof.
  rewrite conj_sym. apply conj_false_l.
Qed.

Lemma entails_conj a b c d
      (ab : a ⊨ b)
      (cd : c ⊨ d) :
  a ∧ c ⊨ b ∧ d.
Proof.
  unfold "∧".
  apply entails_resp_neg, entails_resp_disj.
  all: by apply entails_resp_neg.
Qed.

Lemma equiv_conj a b c d
      (ab : a ⇔ b)
      (cd : c ⇔ d) :
  a ∧ c ⇔ b ∧ d.
Proof.
  specialize entails_conj as ec.
  inv ab.
  inv cd.
  split; basic_solver.
Qed.

Lemma entails_neg φ ψ :
      φ ⊨ ψ <-> ¬ψ ⊨ ¬φ.
Proof.
  split.
  { apply entails_resp_neg. }
  intro HH.
  apply entails_resp_neg in HH.
  by rewrite !elim_dneg in HH.
Qed.


Lemma entails_elim_conj_r χ φ ψ :
      (χ ⊨ φ /\ χ ⊨ ψ) <-> (χ ⊨ φ ∧ ψ).
Proof.
  split; intro A; desf.
  { eapply entails_trans; [| eby apply entails_conj].
    apply equiv_conj_idemp. }
  rewrite entails_neg, (entails_neg χ ψ).
  unfold "∧" in A.
  rewrite <- elim_dneg, <- entails_neg in A.
  now apply entails_elim_disj_r.
Qed.

Lemma entails_elim_conj2 χ φ ψ
      (e1 : φ ⊨ ψ) :
  χ ∧ φ ⊨ χ ∧ ψ.
Proof.
  apply entails_conj; auto.
  apply entails_refl.
Qed.

Lemma entails_elim_conj_l2 φ ψ χ
      (e : ψ ⊨ χ) : φ ∧ ψ ⊨ χ.
Proof.
  unfold "∧".
  eapply entails_trans; [| by apply entails_elim_dneg].
  apply entails_resp_neg.
  eapply entails_trans; [| by apply entails_right_disj].
  by apply entails_resp_neg.
Qed.

Lemma entails_elim_conj_l1 φ ψ χ
      (e : φ ⊨ χ) : φ ∧ ψ ⊨ χ.
Proof.
  rewrite conj_sym.
  by apply entails_elim_conj_l2.
Qed.

Lemma conjA a b c :
  (a ∧ b) ∧ c ⇔ a ∧ b ∧ c.
Proof.
  red_helper.
  splits; ins; desf.
Qed.

Lemma disj_conj_distrib a b c :
  (a ∨ b) ∧ c ⇔ a ∧ c ∨ b ∧ c.
Proof.
  red_helper.
  splits; ins; desf.
Qed.

Lemma conj_true_l a :
  tt ∧ a ⇔ a.
Proof.
  red_helper.
  splits; ins; desf.
Qed.

Add Morphism conj with signature
    entails ==> entails ==> entails as conj_mori.
Proof.
  intros x y xy a b ab.
  apply enatils_resp_conj; desf.
Qed.

Add Morphism conj with signature
    equiv ==> equiv ==> equiv as conj_more.
Proof.
  unfold "⇔".
  now ins; desf; split; eapply conj_mori.
Qed.

Lemma conj_spread φ ψ χ :
  φ ∧ ψ ∧ χ ⇔ (φ ∧ ψ) ∧ (φ ∧ χ).
Proof.
  red_helper.
  split; ins; desf.
Qed.

Lemma conj_spread_list φ l :
  φ ∧ Formula.conj_list l ⇔ φ ∧ Formula.conj_list (map (Formula.conj φ) l).
Proof.
  induction l; ins; desf.
  { easy. }
  rewrite <- conjA, conj_sym.
  rewrite <- conjA, conj_sym with (ψ := φ).
  rewrite IHl.
  red_helper.
  split; ins; desf.
Qed.

Lemma conj_spread_list_nonempty φ l
      (NONEMPTY : l <> []) :
  φ ∧ Formula.conj_list l ⇔ Formula.conj_list (map (Formula.conj φ) l).
Proof.
  destruct l; ins; desf.
  rewrite <- conjA, conj_sym.
  rewrite <- conjA, conj_sym with (ψ := φ).
  rewrite conj_spread_list.
  red_helper.
  split; ins; desf.
Qed.

Lemma conj_true_r ϕ :
  ϕ ∧ Formula.tt ⇔ ϕ.
Proof.
  red_helper.
  split; ins; desf.
Qed.

(**************************)
(* SATISFIABLE PROPERTIES *)
(**************************)

Lemma sat_iff φ :
  satisfiable φ <-> exists locf regf eregf qf, eval locf regf eregf qf φ = true.
Proof.
  unfold satisfiable, entails.
  ins; split; intro Q.
  { apply NNPP.
    intro HH.
    apply Q; ins.
    do 4 eapply not_ex_all_not in HH.
    rewrite implb_false_r.
    eby apply eq_true_not_negb in HH. }
  intro HH.
  desf.
  specialize (HH locf regf eregf qf).
  basic_solver.
Qed.

Lemma sat_conj φ ψ
      (SAT : satisfiable (φ ∧ ψ)):
  satisfiable φ /\ satisfiable ψ.
Proof.
  rewrite !sat_iff in *; desf.
  split; exists locf, regf, eregf, qf; simpls.
  all:
    by rewrite negb_orb, andb_true_iff,
       !negb_true_iff, !negb_false_iff in SAT;
    desc.
Qed.

Lemma sat_disj φ ψ :
  satisfiable φ \/ satisfiable ψ <->
  satisfiable (φ ∨ ψ).
Proof using.
  unfold satisfiable.
  split; intros AA; [intros BB|].
  { apply entails_elim_disj_r in BB; desf. }
  eapply NNPP; intro QQ. apply AA, entails_elim_disj_r.
  apply not_or_and in QQ; desf.
  apply NNPP in QQ, QQ0; desf.
Qed.

Lemma sat_subst_reg φ r m
      (SAT : satisfiable (subst_reg φ r m)) :
  satisfiable φ.
Proof.
  rewrite sat_iff in *; desf.
  rewrite eval_subst_reg in SAT.
  do 4 eexists. apply SAT.
Qed.

Lemma sat_subst_loc φ l m
      (SAT : satisfiable (subst_loc φ l m)) :
  satisfiable φ.
Proof.
  rewrite sat_iff in *; desf.
  rewrite eval_subst_loc in SAT.
  do 4 eexists. apply SAT.
Qed.

Lemma sat_subst_ereg_val φ e v
      (SAT : satisfiable (subst_ereg_val φ e v)) :
  satisfiable φ.
Proof.
  rewrite sat_iff in *; desf.
  rewrite eval_subst_ereg_val in SAT.
  do 4 eexists. apply SAT.
Qed.

Lemma sat_subst_ereg_val_list φ l
      (SAT : satisfiable (subst_ereg_val_list φ l)) :
  satisfiable φ.
Proof.
  induction l; ins; desf.
  eapply IHl, sat_subst_ereg_val; eauto.
Qed.

Lemma sat_subst_q φ x ψ
      (SAT : satisfiable (subst_q φ x ψ)) :
  satisfiable φ.
Proof.
  rewrite sat_iff in *; desf.
  eauto.
  rewrite eval_subst_q in SAT.
  do 4 eexists. apply SAT.
Qed.

Lemma sat_q x :
  satisfiable (q x).
Proof.
  apply sat_iff; do 4 eexists; ins.
  Unshelve. all: ins; apply 42.
Qed.

Lemma subst_q_more_eq x l ψ ψ' (EQ : ψ ⇔ ψ') : subst_q x l ψ ⇔ subst_q x l ψ'.
Proof.
  induction x; ins; desf; try easy.
  { now apply equiv_neg. }
  now rewrite IHx1, IHx2.
Qed.

Add Morphism subst_q with signature
    entails ==> eq ==> equiv ==> entails
      as subst_q_mori.
Proof.
  ins. transitivity (subst_q x y0 y1).
  { now apply subst_q_more_eq. }
  clear dependent x0.
  now red; ins; rewrite !eval_subst_q.
Qed.

Add Morphism subst_q with signature
    equiv ==> eq ==> equiv ==> equiv as subst_q_more.
Proof.
  unfold "⇔".
  now ins; desf; split; eapply subst_q_mori.
Qed.

(************************)
(* TAUTOLOGY PROPERTIES *)
(************************)

Lemma taut_eqEE : forall e, tt ⊨ eqEE e e.
Proof.
  red_helper.
  ins.
  apply PeanoNat.Nat.eqb_refl.
Qed.

Lemma taut_eq_const v1 v2
      (tt : tautology (eqEE (Expr.val v1) (Expr.val v2))) :
  v1 = v2.
Proof.
  unfold tautology, entails in tt.
  simpls.
  eapply NPeano.Nat.eqb_eq.
  eapply tt; eauto.
  ins; constructor.
Qed.

Lemma equiv_true_taut_l φ :
      (tt ⇔ φ) <-> tautology φ.
Proof.
  unfold "⇔".
  split.
  {  basic_solver. }
  split; auto.
  apply entails_true.
Qed.

Lemma impl_taut_is_taut φ ψ
      (TAUT : tautology ψ) : tautology (φ ⇒ ψ).
Proof.
  unfold "⇒".
  eapply entails_trans.
  { eapply entails_right_disj. }
  eapply entails_resp_disj; auto.
  apply entails_refl.
Qed.

Lemma taut_conj ψ ϕ :
  tautology (ψ ∧ ϕ)
  <->
  tautology ψ /\ tautology ϕ.
Proof using.
  split.
  { apply entails_elim_conj_r. }
  ins. apply entails_elim_conj_r; desf.
Qed.

Lemma taut_tt : tautology tt.
Proof using.
  apply entails_refl.
Qed.

Lemma taut_disj φ ψ :
  tautology φ \/ tautology ψ
  ->
  tautology (φ ∨ ψ).
Proof.
  intros [HH | HH]; unfold tautology.
  all: etransitivity; [apply HH|].
  { apply entails_left_disj. }
  apply entails_right_disj.
Qed.

Lemma taut_subst_ereg_val φ e v
      (TAUT : tautology φ) :
  tautology (subst_ereg_val φ e v).
Proof.
  by apply entails_resp_subst_ereg_val
    with (φ := tt) (ψ := φ).
Qed.

Lemma taut_subst_ereg_val_list φ l
      (TAUT : tautology φ) :
  tautology (subst_ereg_val_list φ l).
Proof.
  generalize dependent φ.
  induction l; ins.
  apply taut_subst_ereg_val.
  auto.
Qed.

Lemma taut_satisfiable φ
      (TAUT : tautology φ) :
  satisfiable φ.
Proof.
  intro HH.
  specialize (entails_trans
                tt φ ff
                TAUT HH
                (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => false)).
  basic_solver.
Qed.

Lemma taut_equiv_not_satisfiable_neg φ :
      tautology φ <-> ~ (satisfiable (¬φ)).
Proof.
  split; intros HH.
  { rewrite sat_iff.
    do 4 (apply all_not_not_ex; ins).
    specialize (HH n n0 n1 n2); simpls.
    basic_solver. }
  intros n n0 n1 n2; simpls.
  apply not_false_is_true.
  intro QQ.
  apply HH.
  rewrite sat_iff.
  exists n, n0, n1, n2.
  basic_solver.
Qed.

Add Morphism tautology with signature
  entails ==> Basics.impl as taut_mori.
Proof.
  intros x y xy tx.
  unfold tautology.
  by rewrite <- xy.
Qed.

Add Morphism tautology with signature
  equiv ==> iff as taut_more.
Proof.
  intros x y xy.
  split; apply taut_mori, xy.
Qed.

Add Morphism satisfiable with signature
  entails ==> Basics.impl as satisfiable_mori.
Proof.
  intros x y xy tx.
  unfold satisfiable.
  by rewrite <- xy.
Qed.

Add Morphism satisfiable with signature
  equiv ==> iff as satisfiable_more.
Proof.
  intros x y xy.
  split; apply satisfiable_mori, xy.
Qed.

Add Morphism neg with signature
    equiv ==> equiv as neg_more.
Proof.
  intros x y xy.
  by apply equiv_neg.
Qed.

Add Morphism disj_list with signature
    (Forall2 equiv) ==> equiv as disj_list_more.
Proof.
  intros x y F2EQ.
  induction F2EQ; ins; desf.
  rewrite H, IHF2EQ.
  easy.
Qed.

Add Morphism disj_list with signature
    (Forall2 entails) ==> entails as disj_list_mori.
Proof.
  intros x y F2EQ.
  induction F2EQ; ins; desf.
  rewrite H, IHF2EQ.
  easy.
Qed.

Add Morphism conj_list with signature
    (Forall2 equiv) ==> equiv as conj_list_more.
Proof.
  intros x y F2EQ.
  induction F2EQ; ins; desf.
  rewrite H, IHF2EQ.
  easy.
Qed.

Add Morphism conj_list with signature
    (Forall2 entails) ==> entails as conj_list_mori.
Proof.
  intros x y F2EQ.
  induction F2EQ; ins; desf.
  rewrite H, IHF2EQ.
  easy.
Qed.

#[global]
Hint Resolve taut_tt taut_eqEE :
     taut.

Ltac taut_solver :=
  auto with taut;
  repeat match goal with
         | |- _ ⇔ tt => symmetry
         | |- tt ⇔ _ => apply equiv_true_taut_l
         | |- tautology (_ ⇒ ?X) =>
           try by repeat (apply impl_taut_is_taut); auto with taut
         | |- tautology (?X ∨ ?Y) =>
           try by repeat (apply taut_disj); splits; auto with taut
         | |- tautology (eqEE _ _) =>
           try by repeat (apply taut_eqEE); auto with taut
         end.


Create HintDb formula.
Global Hint Resolve entails_refl : formula.
Global Hint Resolve equiv_refl : formula.
Global Hint Resolve equiv_sym : formula.

Lemma taut_subst_loc_new_reg φ l r
      (NO_REG : ~ (lset (used_regs φ)) r) :
  tautology (subst_loc φ l (Expr.reg r))
  <->
  tautology φ.
Proof.
  rewrite !taut_equiv_not_satisfiable_neg.
  split; intro HH; intro QQ; apply HH.
  { apply sat_iff in QQ; desf; simpls.
    apply sat_iff.
    do 4 eexists.
    simpls.
    erewrite <- eval_subst_loc_new_reg; eauto. }
  apply sat_iff in QQ; desf; simpls.
  apply sat_iff.
  exists (fun y => if BinPos.Pos.eqb l y then regf r else locf y), regf, eregf, qf.
  simpls.
  rewrite <- QQ.
  erewrite eval_subst_loc_new_reg with (l := l); simpls; eauto.
  rewrite (eval_subst_loc locf).
  rewrite Reg.eqb_refl.
  simpls.
  unfold RegFun.find.
  arewrite ((fun x => if Reg.eqb x r then regf r else regf x) = regf).
  { apply functional_extensionality; ins; desf; basic_solver. }
  rewrite eval_subst_loc. simpls. unfold RegFun.find.
  match goal with
  | |- negb (_ ?X _ _ _ _) = negb (_ ?Y _ _ _ _) =>
    arewrite (X = Y)
  end.
  { apply functional_extensionality; ins; desf; basic_solver. }
  done.
Qed.

(**************************)
(* IMPLICATION PROPERTIES *)
(**************************)

Lemma impl_as_disj_remember φ ψ :
  φ ⇒ ψ ⇔ ¬φ ∨ φ ∧ ψ.
Proof.
  red_helper.
  split; ins; desf.
Qed.


Lemma impl_disj_r φ ψ χ :
  (φ ⇒ ψ ∨ χ) ⇔ (φ ⇒ ψ) ∨ (φ ⇒ χ).
Proof.
  unfold "⇔", entails.
  split; ins; unfold implb, negb, orb; basic_solver.
Qed.

Lemma impl_conj_r φ ψ χ :
  (φ ⇒ ψ ∧ χ) ⇔ (φ ⇒ ψ) ∧ (φ ⇒ χ).
Proof.
  unfold "⇔", entails.
  split; ins; unfold implb, negb, orb; basic_solver.
Qed.

(********************)
(* OTHER PROPERTIES *)
(********************)

Lemma entails_impl φ ψ :
  φ ⊨ ψ <-> tautology (φ ⇒ ψ).
Proof.
  split; intro HH.
  {
    unfold "⇒".
    rewrite disj_sym.
    eapply entails_trans.
    { eapply formula_lem. }
    apply entails_resp_disj.
    { reflexivity. }
    by apply entails_resp_neg. }
  (* I believe a proof with syntactical entailment is also possible *)
  unfold tautology, entails in *.
  ins.
  specialize (HH locf regf eregf qf).
  unfold negb, implb in *.
  basic_solver.
Qed.

Lemma entails_resp_subst_ereg_val_list l φ ψ
    (ENT : φ ⊨ ψ) :
      subst_ereg_val_list φ l ⊨ subst_ereg_val_list ψ l.
Proof.
  induction l; auto; simpl.
  by eapply entails_resp_subst_ereg_val.
Qed.

Lemma resp_subst_q φ ψ x χ
    (ENT : φ ⊨ ψ) :
      subst_q φ x χ ⊨ subst_q ψ x χ.
Proof.
  red. ins.
  erewrite !eval_subst_q.
  basic_solver.
Qed.

Lemma formula_de_morgan φ ψ :
  ¬(φ ∨ ψ) ⇔ (¬φ) ∧ (¬ψ).
Proof.
  red_helper; ins; desf.
  basic_solver.
Qed.

Lemma formula_de_morgan2 φ ψ :
  ¬(φ ∧ ψ) ⇔ (¬φ) ∨ (¬ψ).
Proof.
  red_helper; ins; desf.
  basic_solver.
Qed.

Lemma conj_disj_distrib a b c :
  (a ∧ b) ∨ c ⇔ (a ∨ c) ∧ (b ∨ c).
Proof.
  red_helper.
  splits; ins; desf.
Qed.

Lemma conj_impl_weaker_premise φ ψ χ
      (WEAKER : Formula.tautology (φ ⇒ ψ)) :
  φ ∧ (ψ ⇒ χ) ⇔ φ ∧ χ.
Proof.
  red_helper.
  split; ins; desf.
  exfalso.
  eapply taut_equiv_not_satisfiable_neg; eauto.
  apply sat_iff.
  do 4 eexists; ins.
  basic_solver.
Qed.

Lemma conj_impl_disjunctive_premise φ ψ χ
      (DISJ : ~ Formula.satisfiable (φ ∧ ψ)) :
  φ ∧ (ψ ⇒ χ) ⇔ φ.
Proof.
  red_helper.
  split; ins; desf.
  exfalso. apply DISJ, sat_iff.
  do 4 eexists; ins.
  basic_solver.
Qed.

Lemma disj_conj_distrib2 a b c :
  c ∧ (a ∨ b) ⇔ c ∧ a ∨ c ∧ b.
Proof.
  red_helper.
  split; ins; desf.
Qed.

Lemma formula_de_morgan_list l :
  ¬ Formula.disj_list l ⇔ Formula.conj_list (map Formula.neg l).
Proof.
  induction l; ins; desf.
  now rewrite formula_de_morgan, IHl.
Qed.

Lemma formula_de_morgan2_list l :
  ¬ Formula.conj_list l ⇔ Formula.disj_list (map Formula.neg l).
Proof.
  induction l; ins; desf.
  now rewrite formula_de_morgan2, IHl.
Qed.
Lemma disjunctive_neg_x_and_x φ :
  ~ Formula.satisfiable ((¬ φ) ∧ φ).
Proof.
  apply taut_equiv_not_satisfiable_neg.
  rewrite disj_sym.
  apply formula_lem.
Qed.

Lemma disj_list_conj_distrib l φ :
  Formula.disj_list l ∧ φ ⇔ Formula.disj_list (map (fun x => x ∧ φ) l).
Proof.
  induction l; ins; desf.
  now rewrite disj_conj_distrib, IHl.
Qed.

Lemma sat_disj_list l :
  Formula.satisfiable (Formula.disj_list l) <-> Exists Formula.satisfiable l.
Proof.
  induction l; ins.
  { now rewrite Exists_nil; split; ins; apply H. }
  now rewrite Exists_cons, <- sat_disj, IHl.
Qed.

Lemma impl_conj_list_r φ l :
  φ ⇒ Formula.conj_list l ⇔ Formula.conj_list (map (fun x => φ ⇒ x) l).
Proof.
  induction l; ins; desf.
  { taut_solver. }
  now rewrite impl_conj_r, IHl.
Qed.

(* TODO: rename *)
Lemma sat_conj_taut_prem_disj_taut_concl {A} (l : list A) prem concl
      (SAT_CONJ : Formula.satisfiable (Formula.conj_list
                                    (map (fun x => (prem x ⇒ concl x)) l)))
      (TAUT_PREM_DISJ : Formula.tautology (Formula.disj_list (map prem l))) :
  Exists Formula.satisfiable (map concl l).
Proof.
  apply sat_iff in SAT_CONJ. desf.
  apply Exists_exists.
  enough (exists x : t, In x (map concl l) /\
                        eval locf regf eregf qf x = true) as AA.
  { desf. eexists. splits; eauto. apply sat_iff; eauto. }
  specialize (TAUT_PREM_DISJ locf regf eregf qf).
  induction l; ins.
  destruct (eval locf regf eregf qf (concl a)) eqn:BB.
  { exists (concl a). splits; auto. }
  destruct (eval locf regf eregf qf (prem a)) eqn:DDC; ins.
  destruct IHl as [x [IN XX]]; ins.
  2: now eexists; eauto.
  match goal with
  | |- ?X = true => destruct X eqn:CC
  end; ins.
Qed.

Lemma conj_list_single φ :
  Formula.conj_list (cons φ nil) ⇔ φ.
Proof.
  ins.
  now rewrite conj_true_r.
Qed.

Lemma sat_conj_list l :
  Formula.satisfiable (Formula.conj_list l) -> Forall Formula.satisfiable l.
Proof.
  induction l; ins.
  apply sat_conj in H; desf.
  rewrite Forall_cons; basic_solver.
Qed.

Lemma disjunctive_x_and_neg_x φ :
  ~ Formula.satisfiable (φ ∧ (¬ φ)).
Proof.
  rewrite conj_sym.
  apply disjunctive_neg_x_and_x.
Qed.

Lemma impl_impl_disjunctive_premise φ ψ χ
      (DISJUNCTIVE : ~ Formula.satisfiable (φ ∧ ψ)) :
  Formula.tautology (φ ⇒ ψ ⇒ χ).
Proof.
  rewrite impl_as_disj_remember, conj_impl_disjunctive_premise; auto.
  rewrite disj_sym. apply formula_lem.
Qed.

Lemma entails_conj_list φ l (HH : forall ψ (IN : In ψ l), φ ⊨ ψ) : 
  φ ⊨ Formula.conj_list l.
Proof.
  induction l; ins.
  { apply entails_true. }
  apply entails_elim_conj_r; split; auto.
Qed.

Lemma conj_list_entails_in φ l (IN : In φ l) : 
  Formula.conj_list l ⊨ φ.
Proof.
  induction l; ins; desf.
  { now apply entails_elim_conj_l1. } 
  apply entails_elim_conj_l2. intuition.
Qed.

Lemma in_entails_disj_list φ l (IN : In φ l) : 
  φ ⊨ Formula.disj_list l.
Proof.
  induction l; ins; desf.
  { apply entails_left_disj. }
  rewrite IHl; auto. apply entails_right_disj.
Qed.

Lemma conj_list_inclusion l1 l2
      (INCL : lset l1 ⊆₁ lset l2) :
  Formula.conj_list l2 ⊨ Formula.conj_list l1.
Proof.
  induction l1; ins.
  { apply entails_true. }
  apply entails_elim_conj_r. split.
  2: { apply IHl1. etransitivity; [|now apply INCL].
       rewrite lset_cons. eauto with hahn. }
  apply conj_list_entails_in. apply INCL.
  red. now constructor.
Qed.

Lemma conj_list_equiv l1 l2
      (INCL : lset l1 ≡₁ lset l2) :
  Formula.conj_list l1 ⇔ Formula.conj_list l2.
Proof.
  split; apply conj_list_inclusion, INCL.
Qed.

Lemma conj_list_app l1 l2 :
  Formula.conj_list (l1 ++ l2) ⇔ Formula.conj_list l1 ∧ Formula.conj_list l2.
Proof.
  induction l1; ins.
  { now rewrite conj_true_l. }
  rewrite IHl1. now rewrite conj_assoc.
Qed.

Lemma disj_list_inclusion_gen l1 l2
      (INCL : forall ψ (IN : In ψ l1),
          exists φ, 
            << IN' : In φ l2 >> /\
            << EQψ : φ ⇔ ψ >>) :
  Formula.disj_list l1 ⊨ Formula.disj_list l2.
Proof.
  induction l1; ins.
  apply entails_elim_disj_r; split.
  2: { apply IHl1; ins. apply INCL; auto. }
  destruct (INCL a) as [ψ]; auto. desf.
  rewrite <- EQψ. now apply in_entails_disj_list.
Qed.

Lemma disj_list_equiv_gen l1 l2
      (INCL  : forall ψ (IN : In ψ l1),
          exists φ, 
            << IN' : In φ l2 >> /\
            << EQψ : φ ⇔ ψ >>)
      (INCL' : forall ψ (IN : In ψ l2),
          exists φ, 
            << IN' : In φ l1 >> /\
            << EQψ : φ ⇔ ψ >>) :
  Formula.disj_list l1 ⇔ Formula.disj_list l2.
Proof. now split; apply disj_list_inclusion_gen. Qed.

Lemma disj_list_inclusion l1 l2
      (INCL : lset l1 ⊆₁ lset l2) :
  Formula.disj_list l1 ⊨ Formula.disj_list l2.
Proof.
  apply disj_list_inclusion_gen.
  ins. eexists; splits; try easy.
  now apply INCL.
Qed.

Lemma disj_list_equiv l1 l2
      (INCL : lset l1 ≡₁ lset l2) :
  Formula.disj_list l1 ⇔ Formula.disj_list l2.
Proof.
  split; apply disj_list_inclusion, INCL.
Qed.

Lemma taut_conj_list l :
      Formula.tautology (Formula.conj_list l) <-> Forall Formula.tautology l.
Proof.
  induction l; ins.
  now rewrite taut_conj, Forall_cons, IHl.
Qed.

Lemma taut_disj_list l :
  Exists Formula.tautology l -> Formula.tautology (Formula.disj_list l).
Proof.
  induction l; intro QQ; desf; ins.
  { now apply Exists_nil in QQ. }
  rewrite Exists_cons in QQ.
  apply taut_disj.
  desf; [now left | now right; apply IHl].
Qed.

Lemma eval_conj_list locf regf eregf qf l :
  Formula.eval locf regf eregf qf (Formula.conj_list l) =
  forallb id (map (Formula.eval locf regf eregf qf) l).
Proof.
  induction l; ins.
  rewrite IHl.
  unfold negb; desf.
Qed.

Lemma impl_impl_same ϕ ψ :
  ϕ ⇒ (ϕ ⇒ ψ) ⇔ ϕ ⇒ ψ.
Proof.
  red_helper.
  split; ins; desf.
Qed.

Lemma compose_subst_ereg_val_list_subst_reg φ r e v l
      (IN : In (e, v) l)
      (FUNC : func_list l) :
  Formula.subst_ereg_val_list (Formula.subst_reg φ r (Expr.ereg e)) l
  =
  Formula.subst_reg (Formula.subst_ereg_val_list φ l) r (Expr.val v).
Proof.
  induction φ; ins.
  all: rewrite subst_ereg_val_list_alt; ins.
  { rewrite subst_ereg_val_list_alt with (φ := eqEE m n); ins.
    erewrite !Expr.compose_subst_ereg_val_list_subst_reg; eauto. }
  { rewrite subst_ereg_val_list_alt with (φ := eqLE x m); ins.
    erewrite !Expr.compose_subst_ereg_val_list_subst_reg; eauto. }
  { rewrite IHφ. rewrite subst_ereg_val_list_alt with (φ := ¬ φ); ins. }
  rewrite IHφ1, IHφ2. rewrite subst_ereg_val_list_alt with (φ := φ1 ∨ φ2); ins.
Qed.

Lemma subst_ereg_val_list_extract φ e v l
      (IN : In (e, v) l)
      (FUNC : func_list l) :
  Formula.subst_ereg_val_list φ l =
  Formula.subst_ereg_val_list (Formula.subst_ereg_val φ e v) l.
Proof.
  generalize dependent e.
  generalize dependent v.
  induction l; ins; desf; ins.
  2: { erewrite IHl; eauto.
       eapply func_list_cons; eauto. }
  assert (func_list l) as BB.
  { eapply func_list_cons; eauto. }
  destruct (classic (forall p (IN : In p l), fst p <> e)) as [FA|NFA].
  { rewrite subst_ereg_val_list_subst_ereg_val_commute; auto.
    now rewrite subst_ereg_val_idemp. }
  enough (exists p, In p l /\ fst p = e) as EX.
  { destruct EX as [[p p'] IN]; desf. erewrite IHl; eauto; ins.
    enough ((p, v) = (p, p')) as CC.
    { inv CC. }
    apply FUNC; auto.
    { now constructor. }
    now right. }
  clear -NFA BB. induction l; ins.
  { exfalso. apply NFA; ins. }
  destruct (classic (fst a = e)) as [AA|AA].
  { eexists; eauto. }
  destruct IHl as [x HH].
  3: { exists x. desf. split; eauto. }
  { eapply func_list_cons; eauto. }
  intros DD. apply NFA. ins. desf. now apply DD.
Qed.

Lemma subst_q_subst_ereg_val_inject φ x ψ e v :
  subst_ereg_val (Formula.subst_q φ x ψ) e v
  =
  subst_ereg_val (Formula.subst_q φ x (Formula.subst_ereg_val ψ e v)) e v.
Proof.
  induction φ; ins; desf.
  { by rewrite subst_ereg_val_idemp. }
  { by rewrite IHφ. }
  now rewrite IHφ1, IHφ2.
Qed.

Lemma subst_ereg_val_list_nin φ l :
  set_disjoint
    (lset (used_eregs (Formula.subst_ereg_val_list φ l)))
    (lset (map fst l)).
Proof.
  induction l; ins; desf.
  rewrite lset_cons.
  intros e QQ eL.
  destruct eL as [NEW | OLD]; ins; desf.
  { eapply subst_ereg_val_no_ereg; eauto. }
  eapply subst_ereg_val_noereg; eauto.
Qed.

Lemma subst_q_subst_ereg_val_list_inject φ x ψ l:
  subst_ereg_val_list (subst_q φ x ψ) l
  =
  subst_ereg_val_list (subst_q φ x (subst_ereg_val_list ψ l)) l .
Proof.
  induction l; ins; desf.
  assert (set_disjoint
            (lset (used_eregs (subst_ereg_val_list ψ l)))
            (lset (map fst l))) as DISJ.
  { intros e eA eB.
    eapply subst_ereg_val_list_noereg; eauto.
    intro eD.
    eapply subst_ereg_val_list_nin; eauto. }

  rewrite subst_ereg_val_list_subst_q_commute
    with (ψ := subst_ereg_val _ _ _).
  2: { intros e eA eB.
       eapply subst_ereg_val_noereg.
       2: eauto.
       intro eC.
       eapply DISJ; eauto. }
  rewrite IHl.
  rewrite subst_ereg_val_list_subst_q_commute; auto.
  now rewrite <- subst_q_subst_ereg_val_inject.
Qed.

Lemma subst_ereg_val_disj_list l e v :
  subst_ereg_val (disj_list l) e v
  ⇔
  disj_list (map (fun x => subst_ereg_val x e v) l).
Proof.
  induction l; ins; desf.
  now rewrite IHl.
Qed.

End Properties.

End Formula.



