(** Original InitE/SubmissionModel.lean; participant fields contain only
    ROM, score and dispatch metadata, never an evaluator or source program. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words alignment.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.backend Require lab_to_target.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From InitE.Target Require Import ReducedTypes Configuration.
From InitE.Guest Require Import Basic HostMemory.
From InitE.InitE Require Import NatE Parameters MachineInitialization.
Open Scope N_scope.
Record Submission : Type := {
 code : list (word 8);
 K : NatE;
 anchorPc : N;
 names : list ffiname;
 first : N;
 extra : list lab_to_target.shmem_info_num
}.
Definition submissionSharedDomain (a : word 64) : Prop :=
 (inputStart <= w2n a /\ w2n a < inputEnd) \/
 (outputStart <= w2n a /\ w2n a < outputEnd).
Definition submissionMemoryDomain (a : word 64) : Prop :=
 ((initialPc <= w2n a /\ w2n a < initialPc+codeSizeLimit) \/
 (ramStart <= w2n a /\ w2n a < ramEnd)) /\ ~ submissionSharedDomain a.
Definition programDomain (s : Submission) (a : word 64) : Prop :=
 submissionMemoryDomain a /\ forall i, i < first s+2 ->
 a <> (n2w (anchorPc s)-n2w (lab_to_target.ffi_offset*(i+1)))%w.
Definition machineConfig (s : Submission) : machine_config 64 riscv_state RiscVProjection :=
 challengeMachineConfig (n2w (anchorPc s)) (programDomain s) submissionSharedDomain (names s) (first s) (extra s).
Definition initialMemory (s : Submission) (input : InputBlob) (a : word 64) : word 8 :=
 if classical_dec (submissionSharedDomain a) then
 match guestHostMemory input a with Some b => b | None => n2w 0 end else
 if (initialPc <=? w2n a) && (w2n a <? initialPc+LENGTH (code s)) then
 nthN (w2n a-initialPc) (code s) (n2w 0) else n2w 0.
Definition initialState (s : Submission) (input : InputBlob) : riscv_state :=
 riscv_state_exception_fupd (fun _ => NoException)
 (riscv_state_c_NextFetch_fupd (fun _ _ => None)
 (riscv_state_c_gpr_fupd (fun _ _ _ => n2w 0)
 (riscv_state_c_PC_fupd (fun _ _ => n2w initialPc)
 (riscv_state_c_MCSR_fupd (fun _ _ =>
   MachineCSR_mstatus_fupd (fun _ => mstatus_VM_fupd (fun _ => n2w 0)
    (mstatus_MPRV_fupd (fun _ => n2w 3) (inhabitant _)))
   (MachineCSR_mcpuid_fupd (fun _ => mcpuid_ArchBase_fupd (fun _ => n2w 2) (inhabitant _)) (inhabitant _)))
 (riscv_state_MEM8_fupd (fun _ => initialMemory s input) (inhabitant _)))))).
Record Admitted (s : Submission) : Prop := {
 code_nonempty : 0 < LENGTH (code s);
 code_limit : LENGTH (code s) <= codeSizeLimit;
 anchor_lower : initialPc+lab_to_target.ffi_offset*(first s+2) < anchorPc s;
 anchor_upper : anchorPc s < initialPc+LENGTH (code s);
 anchor_aligned : aligned 2 (n2w (anchorPc s) : word 64) = true;
 name_boundary : ffiNameBoundaryValid (names s) (first s);
 metadata_length : LENGTH (names s) = first s+LENGTH (extra s);
 ordinary_slots_loaded : forall i, i < first s+2 ->
 let a : word 64 := (n2w (anchorPc s)-n2w (lab_to_target.ffi_offset*(i+1)))%w in
 initialPc < w2n a /\ w2n a < initialPc+LENGTH (code s);
 mmio_valid : forall i, i < LENGTH (names s) -> first s <= i ->
 mmioRecordValid (n2w (anchorPc s)) (first s) (extra s) i = true;
 entry_distinct : NoDup (ffi_entry_pcs (machineConfig s));
 entry_loaded : forall a, In a (ffi_entry_pcs (machineConfig s)) ->
 initialPc < w2n a /\ w2n a < initialPc+LENGTH (code s);
 entry_aligned : forall a, In a (ffi_entry_pcs (machineConfig s)) -> aligned 2 a = true;
 entry_dispatch_separate : forall a, In a (ffi_entry_pcs (machineConfig s)) ->
 a <> halt_pc (machineConfig s) /\ a <> ccache_pc (machineConfig s);
 mmio_program : forall rec, In rec (extra s) -> programDomain s
 (n2w (anchorPc s)+n2w (lab_to_target.entry_pc rec))%w;
 exit_loaded : forall rec, In rec (extra s) -> anchorPc s+lab_to_target.exit_pc rec < initialPc+LENGTH (code s);
 layout_bound : LENGTH (code s)+lab_to_target.ffi_offset*(first s+3) < 2^64
}.
Theorem initialState_registers s input r :
 riscv_state_c_gpr (initialState s input) (riscv_state_procID (initialState s input)) r = n2w 0.
Proof. reflexivity. Qed.
Theorem initialState_mode s input :
 mstatus_MPRV (MachineCSR_mstatus (riscv_state_c_MCSR (initialState s input)
  (riscv_state_procID (initialState s input)))) = n2w 3 /\
 mstatus_VM (MachineCSR_mstatus (riscv_state_c_MCSR (initialState s input)
  (riscv_state_procID (initialState s input)))) = n2w 0.
Proof. split; reflexivity. Qed.
Theorem initialState_ok s input : riscvOk (initialState s input) = true.
Proof. reflexivity. Qed.
