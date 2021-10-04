From hahn Require Import Hahn.
From imm Require Import Events.

Require Import Basics.
Require Import AuxDef.
Require Import AuxRel.
Require Import Language.

(** This section corresponds to §4.2.
    We introduce actions and relations on them.
*)
Section Action.
Local Open Scope program_scope.

Record action := mk_action
  { imm_lbl : label;
    α : thread_id;
  }.

Definition def_action := mk_action (Afence Opln) tid_init.

Definition mod' := mod id ∘ imm_lbl.

Definition same_mod' := imm_lbl ⋄ same_mod id.

Definition loc' := loc id ∘ imm_lbl.

Definition same_loc' := imm_lbl ⋄ same_loc id.

Definition val' := val id ∘ imm_lbl.

Definition same_val' := imm_lbl ⋄  same_val id.

Definition is_sc' := is_sc id ∘ imm_lbl.

Definition mode_ge (μ : mode) a : bool :=
  mode_le μ a.

Definition is_mode_ge (μ : mode) a : Prop :=
  is_true (mode_ge μ (mod' a)).

Definition is_mode_le (μ : mode) a : Prop :=
  is_true (mode_le μ (mod' a)).


Definition is_w' := is_true ∘ is_w id ∘ imm_lbl.
Definition is_r' := is_true ∘ is_r id ∘ imm_lbl.
Definition is_f' := is_true ∘ is_f id ∘ imm_lbl.

Definition is_release :=
  is_w' ∩₁ is_mode_ge Oacqrel ∪₁
  is_f' ∩₁ is_mode_ge Orel.

Definition is_release_b a :=
  (is_w imm_lbl a) && (mode_ge Oacqrel (mod' a)) ||
  (is_f imm_lbl a) && (mode_ge Orel (mod' a)).

(*************************)
(** Auxiliary relations  *)
(*************************)

Definition matches := is_w' × is_r' ∩ same_loc' ∩ same_val'.

Definition blocks := is_w' × is_r' ∩ same_loc'.

Definition overlaps := same_loc'.

Definition coh_delays :=
  same_loc' ∩ (is_w' × is_w' ∪ is_r' × is_w' ∪ is_w' × is_r') ∪
  is_sc' × is_sc'.

Definition sync_delays :=
  ⊤₁ × (is_w' ∩₁ is_mode_ge Oacqrel) ∪
  ⊤₁ × (is_f' ∩₁ is_mode_ge Orel) ∪
  is_r' × (is_f' ∩₁ is_mode_ge Oacq) ∪
  (is_r' ∩₁ is_mode_ge Oacqrel) × ⊤₁ ∪
  (is_f' ∩₁ is_mode_ge Oacq) × ⊤₁ ∪
  (is_f' ∩₁ is_mode_ge Orel) × is_w' ∪
  same_loc' ∩ ((is_w' ∩₁ is_mode_ge Oacqrel) × is_w').

End Action.
