From hahn Require Import Hahn.
From PromisingLib Require Import Basic.
From imm Require Import Events.
From imm Require Import Prog.
From imm Require Import ProgToExecution.

Require Import Basics.
Require Import Events.
Require Import AuxDef.

Inductive scope :=
| grp
| proc
| sys.

Module Expr.

Inductive t :=
| val  (v : value)
| reg  (r : Reg.t)
| ereg (e : Event.t)
.

Definition eval (rf : RegFile.t) (erf : Event.t -> value)
           (e : t) : value :=
  match e with
  | val  v => v
  | reg  r => RegFun.find r rf
  | ereg e => erf e
  end.

Definition eval_ereg0 (rf : RegFile.t) (e : t) : value :=
  eval rf (fun _ => 0) e.

Definition used_regs (e : t) : list Reg.t :=
  match e with
  | reg r => [r]
  | _ => nil
  end.

Definition deps_set {A} (df : RegFun.t (A -> Prop)) expr e :=
  exists r,
    << UREG : List.In r (used_regs expr) >> /\
    << INDEPF : df r e >>.

Definition deps_set_alt {A} (df : RegFun.t (A -> Prop)) (e : t) : A -> Prop :=
  match e with
  | reg r => df r
  | _     => ∅
  end.

Lemma deps_set_deps_set_alt {A} (df : RegFun.t (A -> Prop)) e :
  deps_set df e ≡₁ deps_set_alt df e.
Proof.
  unfold deps_set.
  induction e; simpls; basic_solver.
Qed.

Definition used_eregs (e : t) : list Event.t :=
  match e with
  | ereg e => [e]
  | _ => nil
  end.

Definition no_eregs (e : t) : Prop :=
  match e with
  | ereg _ => False
  | _      => True
  end.

Lemma no_eregs_used_eregs (e : t)
      (NOEREGS : no_eregs e) :
  used_eregs e = [].
Proof.
  induction e; auto; simpls.
Qed.

Definition subst_reg (e : t) (r : Reg.t) (e' : t) : t :=
  match e with
  | reg r' => if BinPos.Pos.eqb r r' then e' else e 
  | _ => e
  end.

Lemma eval_subst_reg regf eregf e r e' :
  let regf' := fun y =>
                 if BinPos.Pos.eqb r y
                 then eval regf eregf e'
                 else regf y
  in eval regf  eregf (subst_reg e r e') =
     eval regf' eregf e.
Proof.
  induction e; desf.
  unfold subst_reg.
  unfold eval.
  unfold RegFun.find.
  desf; basic_solver.
Qed.

Definition subst_ereg (e : t) (re : Event.t) (e' : t) : t :=
  match e with
  | ereg re' => if Event.eq re re' then e' else e
  | _ => e
  end.

Definition subst_ereg_val_list
           (e : t)
           (l : list (Event.t * value)) : t :=
  List.fold_right
    (fun ev e' => subst_ereg e' (fst ev) (val (snd ev))) e l.


Lemma subst_ereg_val_list_val v l :
  subst_ereg_val_list (val v) l = (val v).
Proof.
  induction l; auto.
  simpl.
  rewrite IHl.
  basic_solver.
Qed.

Lemma no_ereg_subst_ereg m e v
      (NOEREGS: no_eregs m) :
  subst_ereg m e (val v) = m.
Proof.
  induction m; basic_solver.
Qed.

Lemma subst_ereg_no_ereg m e v :
  ~ lset (used_eregs (subst_ereg m e (val v))) e.
Proof.
  induction m; desf; ins.
  desf; ins.
  intro QQ; apply Heq.
  basic_solver.
Qed.

Lemma subst_ereg_val_list_no_eregs m l
      (NOEREGS: no_eregs m) :
  subst_ereg_val_list m l = m.
Proof.
  induction l; auto.
  simpl. rewrite IHl.
  destruct m; ins.
Qed.

Lemma nin_subst_ereg_val_list e l
      (NIN : ~ (lset (List.map fst l)) e) :
  subst_ereg_val_list (ereg e) l = ereg e.
Proof.
  induction l; auto.
  simpls.
  clarify_not.
  rewrite IHl; auto.
  unfold subst_ereg.
  desf; auto.
  basic_solver.
Qed.

Lemma subst_ereg_val_list_ereg e l :
  subst_ereg_val_list (ereg e) l = ereg e
  \/
  exists v',
    In (e, v') l /\
    subst_ereg_val_list (ereg e) l = val v'.
Proof.
  induction l; auto; ins.
  destruct a; ins. desf.
  { rewrite IHl; ins. desf; desf; eauto. }
  rewrite IHl0; ins. eauto. 
Qed.

Lemma eval_subst_ereg_val m regf eregf e v :
  let eregf' := fun e' =>
                  if Event.eq e e'
                  then v
                  else eregf e'
  in
  eval regf eregf (subst_ereg m e (val v)) =
  eval regf eregf' m.
Proof.
  induction m; desf.
  unfold subst_ereg.
  unfold eval.
  desf; basic_solver.
Qed.

Lemma used_regs_subst_reg e r m :
  lset (used_regs (subst_reg e r m)) ≡₁
  lset (used_regs e) \₁ eq r ∪₁
  codom_rel ((lset (used_regs e) ∩₁ eq r) × lset (used_regs m)).
Proof.
  induction e; auto; simpls.
  2: { desf; rewrite lset_cons, lset_empty; basic_solver 10. }
  all: basic_solver.
Qed.

Lemma used_eregs_subst_reg e r m :
  lset (used_eregs (subst_reg e r m)) ≡₁
  lset (used_eregs e) ∪₁
  ifP (lset (used_regs e) r) then lset (used_eregs m) else ∅.
Proof.
  induction e; simpls; desf; basic_solver.
Qed.

Lemma nin_subst_reg e r m
      (NO_REG : ~ (lset (used_regs e)) r) :
  subst_reg e r m = e.
Proof.
  induction e; auto; simpls.
  clarify_not.
  desf; basic_solver.
Qed.

Lemma nin_subst_ereg m e v
      (NO_EREG : ~ (lset (used_eregs m)) e) :
  subst_ereg m e v = m.
Proof.
  induction m; auto; simpls.
  clarify_not.
  desf; basic_solver.
Qed.

Lemma compose_subst_ereg_subst_reg expr r e v :
  subst_ereg (subst_reg expr r (ereg e)) e (val v)
  =
  subst_reg (subst_ereg expr e (val v)) r (val v).
Proof.
  induction expr; simpls; eauto.
  { do 2 (desf; simpls). }
  do 2 desf.
Qed.

Lemma subst_reg_same_reg φ r :
  subst_reg φ r (Expr.reg r) = φ.
Proof.
  induction φ; ins; desf; congruence.
Qed.

Lemma subst_ereg_val_idemp m e v v' :
  subst_ereg (subst_ereg m e (val v)) e (val v') =
  subst_ereg m e (val v).
Proof.
  induction m; simpls; eauto.
  desf; basic_solver.
Qed.

Lemma subst_ereg_val_noereg e φ e' v'
      (NO_EREG :  ~ lset (used_eregs φ) e) :
  ~ lset (used_eregs (subst_ereg φ e' (val v'))) e.
Proof.
  induction φ; simpls; eauto.
  desf; basic_solver.
Qed.

Lemma subst_neq_ereg_val_commute φ e v e' v'
      (NEQ : ~ e = e') :
  subst_ereg (subst_ereg φ e (val v)) e' (val v') =
  subst_ereg (subst_ereg φ e' (val v')) e (val v).
Proof.
  induction φ; simpls; eauto.
  desf; basic_solver.
Qed.

Lemma subst_ereg_val_subst_reg_commute m r m' e v
      (NOEREG : ~ lset (used_eregs m') e) :
  subst_ereg (subst_reg m r m') e (val v) =
  subst_reg (subst_ereg m e (val v)) r m'.
Proof.
  destruct m'; auto.
  1-2: by destruct m; basic_solver.
  destruct m; simpls.
  all: by clarify_not; desf; simpl; desf; basic_solver.
Qed.

Lemma compose_subst_ereg_val_list_subst_reg expr r e v l
      (IN : In (e, v) l)
      (FL : func_list l) :
  subst_ereg_val_list (subst_reg expr r (ereg e)) l
  =
  subst_reg (subst_ereg_val_list expr l) r (val v).
Proof.
  induction l; ins.
  destruct (classic (In (e, v) l)) as [AA|AA].
  { rewrite IHl; auto.
    2: now eapply func_list_cons; eauto.
    destruct a; ins.
    now apply subst_ereg_val_subst_reg_commute. }
  desf; ins.
  clear IHl.
  assert (~ lset (map fst l) e) as NLL.
  { intros HH. red in HH. apply in_map_iff in HH. desf.
    enough (x = (fst x, v)) as DD.
    { destruct x; ins. inv DD. }
    apply FL; ins; auto. }
  induction expr; ins.
  { rewrite subst_ereg_val_list_val; ins. }
  { rewrite subst_ereg_val_list_no_eregs with (m:=reg r0); ins.
    desf; desf.
    2: now rewrite subst_ereg_val_list_no_eregs with (m:=reg r0); ins.
    rewrite nin_subst_ereg_val_list; ins. desf; desf. }
  destruct (classic (e0 = e)) as [|NEE]; subst.
  { rewrite nin_subst_ereg_val_list; ins. desf; desf. }
  edestruct subst_ereg_val_list_ereg as [GG|GG].
  { rewrite !GG; ins. desf; desf. }
  desf. rewrite GG0. ins.
Qed.

End Expr.

Section Language.
Local Open Scope program_scope. (* for ∘ *)
(* Definition expression := Value.t. *)

Definition reg_expr := Value.reg.
Definition const_expr := Value.const.


End Language.

Module Stmt.

Inductive t :=
| skip
| assign (r : Reg.t) (m : Expr.t)
| read (r : Reg.t) (L : location) (μ : mode) (σ : scope)
| write (L : location) (μ : mode) (σ : scope) (m : Expr.t)
| fence (ν : mode) (σ : scope)
| ite (m : Expr.t) (s1 s2 : t)
| seq (s1 s2 : t)
(* | par (s1 s2 : statement) (γ : thread). *)
.

Fixpoint used_regs (s : t) : list Reg.t :=
  match s with
  | assign r m     => r :: (Expr.used_regs m)
  | read   r _ _ _ => [r]
  | write  _ _ _ m => Expr.used_regs m
  | ite    m s1 s2 => (Expr.used_regs m) ++ used_regs s1 ++ used_regs s2
  | seq      s1 s2 => used_regs s1 ++ used_regs s2
  | _ => nil
  end.

Fixpoint used_locs (s : t) : list location :=
  match s with
  | read   _ l _ _ => [l]
  | write  l _ _ m => [l]
  | ite    m s1 s2 => used_locs s1 ++ used_locs s2
  | seq      s1 s2 => used_locs s1 ++ used_locs s2
  | _ => nil
  end.

Fixpoint no_eregs (s : t) : Prop :=
  match s with
  | assign r m     => Expr.no_eregs m 
  | write  _ _ _ m => Expr.no_eregs m
  | ite    m s1 s2 => Expr.no_eregs m /\ no_eregs s1 /\ no_eregs s2
  | seq      s1 s2 => no_eregs s1 /\ no_eregs s2
  | _ => True
  end.
End Stmt.

Module Prog.
  Definition t := IdentMap.t Stmt.t.
End Prog.
