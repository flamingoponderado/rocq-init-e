(** Admission of the original baseline from literal length and metadata facts.
    No compiler-output equality or installed initial state is a premise. *)
From Galette Require Import Base.
From Stdlib Require Import NArith Lia.
From Galette.HOL.src.n_bit Require Import words alignment.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.compiler.backend Require lab_to_target.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From InitE.Guest Require Import Basic.
From InitE.Target Require Import ReducedTypes Configuration.
From InitE.InitE Require Import NatE Parameters MachineInitialization BaselineArtifactLayout SubmissionModel.
From InitE.Baseline Require Import Artifacts ArtifactFacts BootstrapMemory Metadata MetadataFacts Submission.
Open Scope N_scope.

Theorem baselineSubmission_literals :
 SubmissionModel.code baselineSubmission = Artifacts.code /\
 K baselineSubmission = infinity /\ anchorPc baselineSubmission = nativePc /\
 names baselineSubmission = baselineNames /\ first baselineSubmission = baselineFirst /\
 extra baselineSubmission = baselineMmio.
Proof. repeat split; reflexivity. Qed.

Theorem baselineSubmission_code_length :
 LENGTH (SubmissionModel.code baselineSubmission) = baselineRomLength.
Proof.
 change (LENGTH Artifacts.code = fullRomByteCount).
 exact (proj2 (proj2 (proj2 original_literal_sizes))).
Qed.

Theorem baselineSubmission_program_domain :
 programDomain baselineSubmission = BootstrapMemory.bootstrapDomain.
Proof. reflexivity. Qed.

Theorem baselineSubmission_machine_config :
 machineConfig baselineSubmission =
 challengeMachineConfig (n2w nativePc) BootstrapMemory.bootstrapDomain submissionSharedDomain
  baselineNames baselineFirst baselineMmio.
Proof. reflexivity. Qed.

Theorem baselineSubmission_entry_pcs :
 ffi_entry_pcs (machineConfig baselineSubmission) = baselineEntryPcs.
Proof. reflexivity. Qed.

Theorem baselineSubmission_admitted : Admitted baselineSubmission.
Proof.
 destruct baseline_numeric_admission as [Hnonempty [Hlimit [Hlower [Hupper [Halign Hbound]]]]].
 constructor.
 - rewrite baselineSubmission_code_length; exact Hnonempty.
 - rewrite baselineSubmission_code_length; exact Hlimit.
 - exact Hlower.
 - rewrite baselineSubmission_code_length; exact Hupper.
 - exact Halign.
 - exact baseline_name_boundary.
 - exact (proj2 (proj2 (proj2 baseline_metadata_lengths))).
 - intros i Hi; cbn zeta; rewrite baselineSubmission_code_length.
   change (initialPc < w2n ((n2w nativePc-n2w (lab_to_target.ffi_offset*(i+1)))%w : word 64) /\
     w2n ((n2w nativePc-n2w (lab_to_target.ffi_offset*(i+1)))%w : word 64) < initialPc+baselineRomLength).
   replace (lab_to_target.ffi_offset*(i+1)) with ((1+i)*lab_to_target.ffi_offset) by nia.
   exact (baseline_ordinary_slots_loaded i Hi).
 - exact baseline_mmio_valid.
 - rewrite baselineSubmission_entry_pcs; exact baseline_entry_distinct.
 - intros a Ha; rewrite baselineSubmission_entry_pcs in Ha.
   rewrite baselineSubmission_code_length; exact (baseline_entry_loaded a Ha).
 - rewrite baselineSubmission_entry_pcs; exact baseline_entry_aligned.
 - change (forall a, In a baselineEntryPcs ->
     a <> baselineDispatchAddress 0 /\ a <> baselineDispatchAddress 1).
   exact baseline_entry_dispatch_separate.
 - apply baseline_submission_mmio_program; reflexivity.
 - intros rec Hin; rewrite baselineSubmission_code_length; exact (baseline_exit_loaded rec Hin).
 - rewrite baselineSubmission_code_length; exact Hbound.
Qed.

Theorem baselineSubmission_initial_ok input :
 riscvOk (initialState baselineSubmission input) = true.
Proof. exact (initialState_ok baselineSubmission input). Qed.

Theorem baselineSubmission_initial_pc input :
 riscv_state_c_PC (initialState baselineSubmission input)
  (riscv_state_procID (initialState baselineSubmission input)) = n2w initialPc.
Proof. reflexivity. Qed.

Theorem baselineSubmission_initial_registers input r :
 riscv_state_c_gpr (initialState baselineSubmission input)
  (riscv_state_procID (initialState baselineSubmission input)) r = n2w 0.
Proof. exact (initialState_registers baselineSubmission input r). Qed.
