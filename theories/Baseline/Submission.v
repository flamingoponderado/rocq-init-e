(** Original BaselineSubmissionDefinition.lean: fixed literal ROM, infinity
    score and original dispatch metadata. Admission and behavior are separate. *)
From Galette Require Import Base.
From InitE.InitE Require Import NatE BaselineArtifactLayout SubmissionModel.
From InitE.Baseline Require Import Artifacts Metadata.
Definition baselineSubmission : SubmissionModel.Submission :=
 {| SubmissionModel.code := Artifacts.code;
    SubmissionModel.K := infinity;
    SubmissionModel.anchorPc := nativePc;
    SubmissionModel.names := baselineNames;
    SubmissionModel.first := baselineFirst;
    SubmissionModel.extra := baselineMmio |}.
