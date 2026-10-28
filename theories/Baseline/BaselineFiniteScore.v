(** The initial ROM also has a finite score, in the form [VerificationCore]
    checks: its covered runs take finitely many distinct step counts. The bound
    is only shown to exist, not computed. *)
From InitE.InitE Require Import NatE SubmissionModel Challenge.
From InitE.Baseline Require Import Submission BaselineCertificate FiniteScore.

Theorem baseline_finite_score_exists : exists bound,
 Certificate (withScore baselineSubmission (finite bound)) (finite bound).
Proof. exact (finite_certificate_of_infinity baselineSubmission baseline_certificate). Qed.
