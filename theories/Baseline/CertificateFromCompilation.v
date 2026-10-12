(** All semantic and installation obligations are closed; the exact literal
    compiler equality is the remaining computational premise. *)
From Galette Require Import Base.
From Galette.cakeml.compiler.backend Require Import backend lab_to_target.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From Galette.cakeml.compiler.encoders.asm Require Import asmProps.
From InitE.InitE Require Import Challenge NatE BaselineCompiler SourceSemantics.
From InitE.Baseline Require Import Artifacts Metadata Submission BootstrapCertificate PanInstallation NativeCompilerCorrectness.
Open Scope N_scope.
Local Opaque baselineCompilation nativeCode bitmaps.
Theorem baseline_certificate_from_compilation cprime :
 baselineCompilation = (Some (nativeCode,(bitmaps,cprime)),Some 538) ->
 lab_to_target.ffi_names (backend.lab_conf cprime) = Some baselineNames ->
 lab_to_target.shmem_extra (backend.lab_conf cprime) = baselineMmio ->
 Certificate baselineSubmission infinity.
Proof.
 intros Hcomp Hnames Hmmio; apply baseline_certificate_from_native_correctness.
 intros input ms Hrelated out events Hsource.
 rewrite <- Hsource.
 apply (native_baseline_correct input ms cprime Hcomp Hnames Hmmio Hrelated).
 - exact (baseline_pan_installed ms Hrelated).
 - rewrite Hsource; discriminate.
Qed.
