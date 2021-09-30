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

(* Definition event := nat. *)
  (* { *)
  (* event_thread : thread_id; *)
  (* threadlocal_id : nat; *)
  (* }. *)

(* Definition eq_event e e' := *)
(*   Basic.Ident.eqb (event_thread e) (event_thread e') && *)
(*   eqn (threadlocal_id e) (threadlocal_id e'). *)
