(** Original baseline stack limit from the actual native-entry registers. *)
From Galette Require Import Base.
From Stdlib Require Import NArith Lia.
From Galette.HOL.src.n_bit Require Import words.
From Galette.cakeml.compiler.backend Require Import backend data_to_word.
From Galette.cakeml.compiler.backend.proofs Require Import backendProof stack_removeProof.
From Galette.cakeml.compiler.encoders.asm Require Import asmSem asmProps.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From InitE.InitE Require Import Parameters BaselineCompiler SubmissionModel.
From InitE.Target Require Import ReducedTypes Configuration.
From InitE.Baseline Require Import Submission.
Open Scope N_scope.
Theorem baseline_read_limits ms :
 get_reg riscvTarget ms 11 = n2w sourceBase ->
 get_reg riscvTarget ms 12 = n2w stackStart ->
 get_reg riscvTarget ms 13 = n2w ramEnd ->
 read_limits (config riscvTarget) baselineBackendConfig (machineConfig baselineSubmission) ms =
 (2097104,1944059904).
Proof.
 intros H11 H12 H13; unfold read_limits.
 change (get_stack_heap_limit (2*data_to_word.max_heap_limit 64 (backend.data_conf baselineBackendConfig)-1)
 (get_reg riscvTarget ms 11,(get_reg riscvTarget ms 12,get_reg riscvTarget ms 13)) = (2097104,1944059904)).
 rewrite H11,H12,H13; vm_compute; reflexivity.
Qed.
Theorem baseline_related_read_limits s ms : target_state_rel riscvTarget s ms ->
 regs s 11 = n2w sourceBase -> regs s 12 = n2w stackStart -> regs s 13 = n2w ramEnd ->
 read_limits (config riscvTarget) baselineBackendConfig (machineConfig baselineSubmission) ms =
 (2097104,1944059904).
Proof.
 intros [_ [_ [_ [Hregs _]]]] H11 H12 H13; apply baseline_read_limits.
 - rewrite (Hregs 11 ltac:(vm_compute; intuition congruence)); exact H11.
 - rewrite (Hregs 12 ltac:(vm_compute; intuition congruence)); exact H12.
 - rewrite (Hregs 13 ltac:(vm_compute; intuition congruence)); exact H13.
Qed.
Theorem baseline_stack_bound ms :
 get_reg riscvTarget ms 11 = n2w sourceBase ->
 get_reg riscvTarget ms 12 = n2w stackStart ->
 get_reg riscvTarget ms 13 = n2w ramEnd ->
 538 < fst (read_limits (config riscvTarget) baselineBackendConfig (machineConfig baselineSubmission) ms).
Proof.
 intros H11 H12 H13; rewrite (baseline_read_limits ms H11 H12 H13); vm_compute; congruence.
Qed.
