(** Original InitE/Challenge.lean statement, with fixed source/evaluator.
    No extra input-size premise or weakened finite-termination condition. *)
From Galette Require Import Base.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From InitE.Guest Require Import GasLimit.
From InitE.InitE Require Import NatE Parameters SubmissionModel SourceSemantics Observations TargetTotality.
Open Scope N_scope.
Definition matchingExecutionAt (submission : Submission) (input : InputBlob)
 (out : outcome) (events : list io_event) (steps : N) : Prop :=
 exists targetOutcome post finalFfi,
 evaluate (machineConfig submission) (sourceFfi input) steps (initialState submission input) =
 (Halt targetOutcome,(post,finalFfi)) /\
 matchingResult input out events targetOutcome (io_events finalFfi).
Record Certificate (submission : Submission) (claimed : NatE) : Prop := {
 score : K submission = claimed;
 admitted : Admitted submission;
 correct : forall input : InputBlob, declaredGasLimit input <= 200000000 ->
 forall out events, sourceBehaviour input = Terminate out events ->
 coveredOutcome out -> Within claimed (matchingExecutionAt submission input out events)
}.
Theorem certificate_of_exact_behaviour submission :
 K submission = infinity -> Admitted submission ->
 (forall input out events, sourceBehaviour input = Terminate out events ->
 forall b, machine_sem (machineConfig submission) (sourceFfi input) (initialState submission input) b -> b = Terminate out events) ->
 Certificate submission infinity.
Proof.
 intros HS HA HC; constructor; [exact HS|exact HA|].
 intros input HG out events HSource HCovered.
 pose proof (target_termination_of_behaviour_eq (machineConfig submission) (sourceFfi input)
  (initialState submission input) out events (HC input out events HSource)) as HT.
 cbn [machine_sem] in HT; destruct HT as [steps [post [finalFfi [HE HTrace]]]].
 exists steps; split; [exact I|].
 exists out,post,finalFfi; split; [exact HE|].
 rewrite HTrace; apply matchingResult_refl; exact HCovered.
Qed.
