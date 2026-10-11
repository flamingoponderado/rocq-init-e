(** Precompiled verifier interface. The expected proposition is resolved
    here before any participant module is loaded. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.InitE Require Import NatE SubmissionModel Challenge.
Module Type Literals.
 Parameter submittedCode : list (word 8).
 Parameter claimedScore : NatE.
End Literals.
Module Check (L : Literals).
 Module Type Candidate.
  Parameter submission : Submission.
  Parameter certificate : Certificate
   (Build_Submission L.submittedCode L.claimedScore (anchorPc submission)
    (names submission) (first submission) (extra submission)) L.claimedScore.
 End Candidate.
 Module Accept (C : Candidate).
  Definition checked := C.certificate.
 End Accept.
End Check.
