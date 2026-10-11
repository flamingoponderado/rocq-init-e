(** Preserve PR25's bound rejection and original OOM coverage classes. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics.ffi Require Import ffi.
From InitE.InitE Require Import Observations.
Open Scope N_scope.
Open Scope hol_string_scope.
Example trap_8_covered : coveredOutcome
 (FFI_outcome (Final_event (ExtCall (strlit "trap")) (REPLICATE 8 (n2w 0)) [] FFI_failed)).
Proof. unfold coveredOutcome; split; [reflexivity|right; repeat split; vm_compute; discriminate]. Qed.
Example trap_1_excluded : ~ coveredOutcome
 (FFI_outcome (Final_event (ExtCall (strlit "trap")) (REPLICATE 1 (n2w 0)) [] FFI_failed)).
Proof.
 unfold coveredOutcome; intros [_ [H|[H _]]]; apply H; vm_compute; reflexivity.
Qed.
Example resource_limit_excluded : ~ coveredOutcome Resource_limit_hit.
Proof. exact (fun H => H). Qed.
