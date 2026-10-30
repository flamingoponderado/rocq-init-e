(** Every certified score is at least 3.

    The source semantics accepts the witness [Witness.Input.input]: the
    computable evaluator, run by [vm_compute] at clock 32000, halts through
    [halt] with output byte 32 set, and [EvaluatorCorrect] and [SourceRun]
    turn that run into [sourceBehaviour input].  [TargetLowerBound] then
    shows that a target run matching it needs at least three ticks. *)
From Stdlib Require Import FMapPositive Lia.
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.string Require Import string.
From Galette.HOL.src.finite_maps Require Import finite_map.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.pancake Require Import panLang.
From Galette.cakeml.pancake.semantics Require Import panSem.
From InitE.Guest Require Import Ast GasLimit HostMemory.
From InitE.InitE Require Import NatE Parameters SubmissionModel SourceSemantics Observations Challenge.
From InitE.Witness Require Import Evaluator EvaluatorCorrect SourceDomains SourceRun Input
  TargetLowerBound Runner.
Open Scope N_scope.
Open Scope hol_string_scope.

Definition witnessClock : N := 32000.

(** The only computation: about 200 s of [vm_compute].  The run halts with no
    configuration bytes, and output byte 32 is 1. *)
Lemma witness_check :
  match runInput witnessClock 33 input with
  | {| outcome := Halted [] []; output := out |} => w2n (List.nth 32 out (n2w 0)) =? 1
  | _ => false
  end = true.
Proof. vm_compute; reflexivity. Qed.

Definition haltEvent : final_event := Final_event (ffi.ExtCall (strlit "halt")) [] [] FFI_failed.

Theorem witness_behaviour : exists events,
  sourceBehaviour input = Terminate (FFI_outcome haltEvent) events /\
  outputByte input events acceptanceOffset = n2w 1.
Proof.
  pose proof witness_check as C; revert C.
  pose proof (runInput_halted witnessClock 33 input) as H; revert H.
  destruct (runInput witnessClock 33 input) as [o cu ec out]; cbn [outcome output].
  destruct o as [[|? ?] [|? ?]| | | |]; try discriminate.
  intros H C; destruct (H [] [] eq_refl) as (events & source & bytes).
  exists events; split; [exact source|].
  rewrite (bytes acceptanceOffset) by (cbn; lia).
  change (N.to_nat (offsetValue acceptanceOffset)) with 32%nat.
  apply N.eqb_eq in C. apply word_eq_w2n. rewrite C. reflexivity.
Qed.

Lemma witness_gas : declaredGasLimit input <= 200000000.
Proof. vm_compute; discriminate. Qed.

Lemma witness_initially_clear : outputByte input [] acceptanceOffset <> n2w 1.
Proof. intros E; apply (f_equal w2n) in E; vm_compute in E; discriminate E. Qed.

Lemma halt_covered : coveredOutcome (FFI_outcome haltEvent).
Proof. split; [reflexivity|left; discriminate]. Qed.

Theorem certificate_score_at_least_three {s claimed} (certificate : Certificate s claimed) :
  Allows claimed 3.
Proof.
  destruct witness_behaviour as (events & source & accepted).
  exact (score_at_least_three_of_accepted certificate input witness_gas witness_initially_clear
    _ events source halt_covered (conj (conj eq_refl eq_refl) accepted)).
Qed.

Theorem certificate_finite_score_at_least_three {s k} (certificate : Certificate s (finite k)) :
  3 <= k.
Proof. exact (certificate_score_at_least_three certificate). Qed.

Theorem submission_score_at_least_three {s claimed} (certificate : Certificate s claimed) :
  Allows (K s) 3.
Proof. rewrite (score s claimed certificate); exact (certificate_score_at_least_three certificate). Qed.
