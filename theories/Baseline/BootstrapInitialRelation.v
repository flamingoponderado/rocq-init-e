(** Actual submitted startup state related to the original bootstrap ASM state.
    Original BaselineSubmissionDefinition/StartupEnvironment interfaces. Shared
    bytes remain the host overlay; no input-size or installed-state premise. *)
From Galette Require Import Base.
From Stdlib Require Import NArith Lia.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From InitE.Target Require Import ReducedTypes Configuration.
From InitE.Guest Require Import Basic GasLimit HostMemory.
From InitE.InitE Require Import Parameters BaselineArtifactLayout MachineInitialization SubmissionModel.
From InitE.Baseline Require Import Artifacts BootstrapMemory Submission SubmissionFacts.
Open Scope N_scope.
Local Opaque Artifacts.code.

Theorem baseline_initial_memory_overlay (input : InputBlob) a :
 initialMemory baselineSubmission input a =
 if classical_dec (submissionSharedDomain a) then
  match guestHostMemory input a with Some byte => byte | None => n2w 0 end
 else romMemory a.
Proof. unfold initialMemory,romMemory; destruct (classical_dec (submissionSharedDomain a)); reflexivity. Qed.
Theorem baseline_initial_memory_rom (input : InputBlob) a :
 ~ submissionSharedDomain a -> initialMemory baselineSubmission input a = romMemory a.
Proof.
 intro Houtside; rewrite baseline_initial_memory_overlay;
 destruct (classical_dec (submissionSharedDomain a)); [contradiction|reflexivity].
Qed.
Theorem baseline_initial_memory_shared (input : InputBlob) a :
 submissionSharedDomain a -> initialMemory baselineSubmission input a =
 match guestHostMemory input a with Some byte => byte | None => n2w 0 end.
Proof.
 intro Hshared; rewrite baseline_initial_memory_overlay;
 destruct (classical_dec (submissionSharedDomain a)); [reflexivity|contradiction].
Qed.
Theorem baseline_initial_input_frame (input : InputBlob) a :
 inputStart <= w2n a -> w2n a < inputEnd ->
 riscv_state_MEM8 (initialState baselineSubmission input) a =
 nthN (w2n a-inputStart) (hostInputBytes input) (n2w 0).
Proof.
 intros Hlo Hhi; change (initialMemory baselineSubmission input a = nthN (w2n a-inputStart) (hostInputBytes input) (n2w 0)).
 rewrite baseline_initial_memory_shared by (left; split; assumption).
 unfold guestHostMemory; cbn zeta.
 assert (Hguard : (inputStart <=? w2n a) && (w2n a <? inputEnd) = true)
  by (apply andb_true_iff; split; [apply N.leb_le|apply N.ltb_lt]; assumption).
 rewrite Hguard; reflexivity.
Qed.
Theorem baseline_initial_output_frame (input : InputBlob) a :
 outputStart <= w2n a -> w2n a < outputEnd ->
 riscv_state_MEM8 (initialState baselineSubmission input) a = n2w 0.
Proof.
 intros Hlo Hhi; change (initialMemory baselineSubmission input a = n2w 0).
 rewrite baseline_initial_memory_shared by (right; split; assumption).
 unfold guestHostMemory; cbn zeta.
 assert (Hapart : inputEnd <= outputStart) by (vm_compute; discriminate).
 assert (Hinput : (w2n a <? inputEnd) = false) by (apply N.ltb_ge; lia).
 assert (Houtput : (outputStart <=? w2n a) && (w2n a <? outputEnd) = true)
  by (apply andb_true_iff; split; [apply N.leb_le|apply N.ltb_lt]; assumption).
 rewrite Hinput,andb_false_r,Houtput; reflexivity.
Qed.
Theorem baseline_initial_overlay_frame (input other : InputBlob) a :
 ~ submissionSharedDomain a ->
 riscv_state_MEM8 (initialState baselineSubmission input) a =
 riscv_state_MEM8 (initialState baselineSubmission other) a.
Proof.
 intro Houtside; change (initialMemory baselineSubmission input a = initialMemory baselineSubmission other a).
 rewrite !baseline_initial_memory_rom by exact Houtside; reflexivity.
Qed.
Theorem baseline_initial_domain_memory (input : InputBlob) a : bootstrapDomain a ->
 riscv_state_MEM8 (initialState baselineSubmission input) a = romMemory a.
Proof.
 intros [[_ Houtside] _]; change (initialMemory baselineSubmission input a = romMemory a).
 apply baseline_initial_memory_rom; exact Houtside.
Qed.
Theorem baseline_rom_ram_zero a : ramStart <= w2n a -> romMemory a = n2w 0.
Proof.
 intro Hram; pose proof baselineSubmission_code_length as Hlength.
 change (LENGTH Artifacts.code = fullRomByteCount) in Hlength.
 unfold romMemory; rewrite Hlength.
 assert (Hend : initialPc+fullRomByteCount < ramStart) by (vm_compute; reflexivity).
 assert (Hguard : (w2n a <? initialPc+fullRomByteCount) = false) by (apply N.ltb_ge; lia).
 rewrite Hguard,andb_false_r; reflexivity.
Qed.
Theorem baseline_initial_ordinary_ram_zero (input : InputBlob) a :
 ramStart <= w2n a -> ~ submissionSharedDomain a ->
 riscv_state_MEM8 (initialState baselineSubmission input) a = n2w 0.
Proof.
 intros Hram Houtside; change (initialMemory baselineSubmission input a = n2w 0).
 rewrite baseline_initial_memory_rom by exact Houtside; apply baseline_rom_ram_zero; exact Hram.
Qed.

Theorem baseline_initial_relation (input : InputBlob) :
 target_state_rel riscvTarget initialAsm (initialState baselineSubmission input).
Proof.
 unfold target_state_rel; apply conj.
 - exact (baselineSubmission_initial_ok input).
 - apply conj.
   + exact (baselineSubmission_initial_pc input).
   + apply conj.
     * intros a Ha; exact (baseline_initial_domain_memory input a Ha).
     * apply conj.
       -- intros i Hi; exact (baselineSubmission_initial_registers input (n2w i)).
       -- intros i Hi; change (i < 0) in Hi; lia.
Qed.
Theorem baseline_machine_target : target (machineConfig baselineSubmission) = riscvTarget.
Proof. reflexivity. Qed.
Theorem baseline_machine_domain :
 prog_addresses (machineConfig baselineSubmission) = mem_domain initialAsm.
Proof. reflexivity. Qed.
Theorem baseline_machine_identity :
 next_interfer (machineConfig baselineSubmission) = (fun _ state => state).
Proof. reflexivity. Qed.
Theorem baseline_machine_shared_domain :
 shared_addresses (machineConfig baselineSubmission) = submissionSharedDomain.
Proof. reflexivity. Qed.
Theorem baseline_initial_interference_ok :
 interference_ok (next_interfer (machineConfig baselineSubmission))
  (proj riscvTarget (mem_domain initialAsm)).
Proof. intros count state; reflexivity. Qed.
