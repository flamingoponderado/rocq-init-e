(** Lower bounds for accepting target runs (InitE/ScoreLowerBound.lean).

    A halting target evaluation with at most two clock ticks that starts in
    ordinary code records no foreign call: a returning call still needs a tick
    to halt.  An accepting run must change the initially clear success byte,
    so it needs at least three ticks.  The certificate corollary takes an
    accepted source witness explicitly. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.backend Require lab_to_target.
From Galette.cakeml.compiler.encoders.asm Require Import asmProps.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From InitE.Guest Require Import GasLimit.
From InitE.InitE Require Import NatE Parameters SubmissionModel MachineInitialization
  SourceSemantics Observations Challenge.
Open Scope N_scope.

Section Short.
Context {a : N} {B C Ffi : Type}.

Ltac split_run H :=
  repeat match type of H with
  | context [match ?x with _ => _ end] => destruct x
  end.

Lemma evaluate_zero (mc : machine_config a B C) (ffi : ffi_state Ffi) ms :
  evaluate mc ffi 0 ms = (TimeOut, (ms, ffi)).
Proof. reflexivity. Qed.

(** One tick can halt only without calling out successfully. *)
Lemma halt_one_preserves_ffi (mc : machine_config a B C) (ffi : ffi_state Ffi) ms out post finalFfi :
  evaluate mc ffi 1 ms = (Halt out, (post, finalFfi)) -> finalFfi = ffi.
Proof.
  intros H; rewrite evaluate_eqn in H; cbn [N.eqb Pos.eqb] in H.
  unfold evaluate_body in H; cbn beta iota zeta in H.
  change (1 - 1) with 0 in H; rewrite ?evaluate_zero in H.
  split_run H; rewrite ?evaluate_zero in H; congruence.
Qed.

Lemma halt_two_preserves_ffi (mc : machine_config a B C) (ffi : ffi_state Ffi) ms steps out post finalFfi :
  steps <= 2 ->
  get_pc (target mc) ms IN (prog_addresses mc DIFF set (ffi_entry_pcs mc)) ->
  evaluate mc ffi steps ms = (Halt out, (post, finalFfi)) -> finalFfi = ffi.
Proof.
  intros Hk Hentry H.
  destruct (N.eq_dec steps 0) as [->|Hnz]; [discriminate H|].
  rewrite evaluate_eqn in H; apply N.eqb_neq in Hnz; rewrite Hnz in H.
  unfold evaluate_body in H.
  destruct (classical_dec _) as [_|Hn]; [|contradiction].
  destruct (classical_dec _); [|discriminate H].
  destruct (apply_oracle _ _) as [ms2 oracle]; cbn zeta in H.
  destruct (classical_dec _); [|discriminate H].
  apply N.eqb_neq in Hnz.
  destruct (N.eq_dec (steps - 1) 0) as [E|E]; [rewrite E in H; discriminate H|].
  replace (steps - 1) with 1 in H by lia.
  eapply halt_one_preserves_ffi; exact H.
Qed.
End Short.

Lemma w2n_initialPc : w2n (n2w initialPc : word 64) = initialPc.
Proof. reflexivity. Qed.

Lemma initial_pc (s : Submission) (input : InputBlob) :
  get_pc (target (machineConfig s)) (initialState s input) = n2w initialPc.
Proof. reflexivity. Qed.

Lemma initial_program (s : Submission) (admitted : Admitted s) : programDomain s (n2w initialPc).
Proof.
  split.
  - unfold submissionMemoryDomain, submissionSharedDomain; rewrite w2n_initialPc.
    cbv [initialPc codeSizeLimit inputStart inputEnd inputSize outputStart outputEnd outputSize]. lia.
  - intros i Hi E. destruct (ordinary_slots_loaded s admitted i Hi) as [Hlt _].
    rewrite <- E, w2n_initialPc in Hlt; lia.
Qed.

Lemma initial_not_entry (s : Submission) (admitted : Admitted s) :
  ~ In (n2w initialPc : word 64) (ffi_entry_pcs (machineConfig s)).
Proof.
  intros Hl. destruct (entry_loaded s admitted _ Hl) as [Hlt _].
  rewrite w2n_initialPc in Hlt; lia.
Qed.

(** Admission forces the first clock tick to execute ordinary code. *)
Lemma entry_is_program (s : Submission) (admitted : Admitted s) (input : InputBlob) :
  get_pc (target (machineConfig s)) (initialState s input) IN
    (prog_addresses (machineConfig s) DIFF set (ffi_entry_pcs (machineConfig s))).
Proof.
  rewrite initial_pc; split; [exact (initial_program s admitted)|].
  unfold pred_set.IN; intros Hin; apply (initial_not_entry s admitted).
  revert Hin; generalize (ffi_entry_pcs (machineConfig s)); intros l.
  induction l as [|y l IH]; cbn; [tauto|]. intros [->|Hy]; [left; reflexivity|right; auto].
Qed.

(** An accepting target execution must change the initially clear success
    byte, so it needs at least three ticks: ordinary entry, a returning call,
    and halt. *)
Theorem accepted_execution_steps (s : Submission) (admitted : Admitted s) (input : InputBlob)
    (initial : outputByte input [] acceptanceOffset <> n2w 1)
    (steps : N) out post finalFfi :
  evaluate (machineConfig s) (sourceFfi input) steps (initialState s input) = (Halt out, (post, finalFfi)) ->
  acceptedOutput input out (io_events finalFfi) -> 3 <= steps.
Proof.
  intros run accepted.
  destruct (N.le_gt_cases 3 steps) as [|short]; [assumption|exfalso].
  pose proof (halt_two_preserves_ffi _ _ _ steps _ _ _ ltac:(lia)
    (entry_is_program s admitted input) run) as E.
  apply initial; rewrite E in accepted; exact (proj2 accepted).
Qed.

(** A matching execution for an accepted source result needs at least three ticks. *)
Theorem matchingExecutionAt_steps (s : Submission) (admitted : Admitted s) (input : InputBlob)
    (initial : outputByte input [] acceptanceOffset <> n2w 1)
    out events (accepted : acceptedOutput input out events) steps :
  matchingExecutionAt s input out events steps -> 3 <= steps.
Proof.
  intros (targetOutcome & post & finalFfi & run & matching).
  unfold matchingResult in matching; destruct (classical_dec _) as [_|Hn]; [|contradiction].
  exact (accepted_execution_steps s admitted input initial steps targetOutcome post finalFfi
    run (proj1 matching)).
Qed.

(** An accepted covered source witness rules out every certified score below 3. *)
Theorem score_at_least_three_of_accepted {s claimed} (certificate : Certificate s claimed)
    (input : InputBlob) (gas : declaredGasLimit input <= 200000000)
    (initial : outputByte input [] acceptanceOffset <> n2w 1)
    out events (source : sourceBehaviour input = Terminate out events)
    (covered : coveredOutcome out) (accepted : acceptedOutput input out events) :
  Allows claimed 3.
Proof.
  destruct (correct s claimed certificate input gas out events source covered) as (steps & bound & execution).
  pose proof (matchingExecutionAt_steps s (admitted s claimed certificate) input initial out events
    accepted steps execution) as lower.
  destruct claimed as [k|]; [|exact I]. cbn [Allows] in bound |- *. lia.
Qed.
