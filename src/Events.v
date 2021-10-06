From hahn Require Import Hahn.
From imm Require Import Events.

Definition tid_init := BinNums.xH.

Module Event.
  Definition t := nat.
  
  Definition eq (e e' : t) := eqn e e'.

  Definition fresh (events : list t) :=
    1 + (fold_right max 0 events).

  Lemma eq_refl e : eq e e.
  Proof.
    unfold eq.
    by rewrite eqnE.
  Qed.

End Event.
