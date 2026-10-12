(** Completion bridge: native endpoint correctness yields the unchanged challenge. *)
From Galette Require Import Base.
From Galette.cakeml.compiler.encoders.asm Require Import asmProps.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From Galette.cakeml.semantics.ffi Require Import ffi.
From InitE.Guest Require Import Basic GasLimit.
From InitE.Target Require Import Configuration.
From InitE.InitE Require Import Challenge NatE Observations SubmissionModel SourceSemantics TargetTotality.
From InitE.Baseline Require Import Submission SubmissionFacts BootstrapCopyChecked BootstrapFfiTrace BootstrapComposition.
Theorem baseline_certificate_from_native_correctness :
 (forall input ms, target_state_rel riscvTarget bootstrapEndpoint ms ->
  forall out events, sourceBehaviour input = Terminate out events ->
  forall b, machine_sem (machineConfig baselineSubmission) (sourceFfi input) ms b ->
   b = Terminate out events) ->
 Certificate baselineSubmission infinity.
Proof.
 intro Hnative; constructor.
 - reflexivity.
 - exact baselineSubmission_admitted.
 - intros input Hgas out events Hsource Hcovered.
   destruct (full_bootstrap_clock_shift input (sourceFfi input))
    as [count [ms2 [Hshift [Hrelated Hdomain]]]].
   pose proof (target_termination_of_behaviour_eq (machineConfig baselineSubmission)
    (sourceFfi input) ms2 out events (Hnative input ms2 Hrelated out events Hsource)) as Hterm.
   pose proof (termination_from_clock_shift (machineConfig baselineSubmission)
    (sourceFfi input) count (initialState baselineSubmission input) ms2 out events Hshift Hterm) as Hinitial.
   cbn [machine_sem] in Hinitial; destruct Hinitial as [steps [post [finalFfi [Heval Htrace]]]].
   exists steps; split; [exact I|]. exists out,post,finalFfi; split; [exact Heval|].
   rewrite Htrace; apply matchingResult_refl; exact Hcovered.
Qed.
