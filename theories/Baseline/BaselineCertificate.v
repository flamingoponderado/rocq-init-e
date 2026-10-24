(** Unconditional certificate for the pinned original baseline. *)
From InitE.InitE Require Import Challenge NatE.
From InitE.Baseline Require Import Submission CompilationCertificate CertificateFromCompilation.
Theorem baseline_certificate : Certificate baselineSubmission infinity.
Proof.
 destruct concrete_compilation as [configuration [Hcompile [Hnames Hmmio]]].
 exact (baseline_certificate_from_compilation configuration Hcompile Hnames Hmmio).
Qed.
