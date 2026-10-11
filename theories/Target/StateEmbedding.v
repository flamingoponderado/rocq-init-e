(** Embedding of original reduced state into the compiler proof model.
    Extra full-model fields are initialized here, never added to the
    challenge state carrier or its canonical unspecified value. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From InitE.Target Require Import ReducedTypes.
Open Scope N_scope.
Definition embedrawInstType (x : ReducedTypes.rawInstType) : riscv.rawInstType :=
 match x with
 | ReducedTypes.Half value => riscv.Half (value)
 | ReducedTypes.Word value => riscv.Word (value)
 end.
Definition embedaccessType (x : ReducedTypes.accessType) : riscv.accessType :=
 match x with
 | ReducedTypes.Read => riscv.Read
 | ReducedTypes.Write => riscv.Write
 end.
Definition embedfetchType (x : ReducedTypes.fetchType) : riscv.fetchType :=
 match x with
 | ReducedTypes.Instruction => riscv.Instruction
 | ReducedTypes.Data => riscv.Data
 end.
Definition embedArchitecture (x : ReducedTypes.Architecture) : riscv.Architecture :=
 match x with
 | ReducedTypes.RV32I => riscv.RV32I
 | ReducedTypes.RV64I => riscv.RV64I
 | ReducedTypes.RV128I => riscv.RV128I
 end.
Definition embedPrivilege (x : ReducedTypes.Privilege) : riscv.Privilege :=
 match x with
 | ReducedTypes.User => riscv.User
 | ReducedTypes.Supervisor => riscv.Supervisor
 | ReducedTypes.Hypervisor => riscv.Hypervisor
 | ReducedTypes.Machine => riscv.Machine
 end.
Definition embedVM_Mode (x : ReducedTypes.VM_Mode) : riscv.VM_Mode :=
 match x with
 | ReducedTypes.Mbare => riscv.Mbare
 | ReducedTypes.Mbb => riscv.Mbb
 | ReducedTypes.Mbbid => riscv.Mbbid
 | ReducedTypes.Sv32 => riscv.Sv32
 | ReducedTypes.Sv39 => riscv.Sv39
 | ReducedTypes.Sv48 => riscv.Sv48
 | ReducedTypes.Sv57 => riscv.Sv57
 | ReducedTypes.Sv64 => riscv.Sv64
 end.
Definition embedExtStatus (x : ReducedTypes.ExtStatus) : riscv.ExtStatus :=
 match x with
 | ReducedTypes.Off => riscv.Off
 | ReducedTypes.Initial => riscv.Initial
 | ReducedTypes.Clean => riscv.Clean
 | ReducedTypes.Dirty => riscv.Dirty
 end.
Definition embedExceptionType (x : ReducedTypes.ExceptionType) : riscv.ExceptionType :=
 match x with
 | ReducedTypes.Fetch_Misaligned => riscv.Fetch_Misaligned
 | ReducedTypes.Fetch_Fault => riscv.Fetch_Fault
 | ReducedTypes.Illegal_Instr => riscv.Illegal_Instr
 | ReducedTypes.Breakpoint => riscv.Breakpoint
 | ReducedTypes.Load_Fault => riscv.Load_Fault
 | ReducedTypes.AMO_Misaligned => riscv.AMO_Misaligned
 | ReducedTypes.Store_AMO_Fault => riscv.Store_AMO_Fault
 | ReducedTypes.UMode_Env_Call => riscv.UMode_Env_Call
 | ReducedTypes.SMode_Env_Call => riscv.SMode_Env_Call
 | ReducedTypes.HMode_Env_Call => riscv.HMode_Env_Call
 | ReducedTypes.MMode_Env_Call => riscv.MMode_Env_Call
 end.
Definition embedmcpuid (x : ReducedTypes.mcpuid) : riscv.mcpuid :=
 {| riscv.mcpuid_ArchBase := ReducedTypes.mcpuid_ArchBase x;
    riscv.mcpuid_I := ReducedTypes.mcpuid_I x;
    riscv.mcpuid_M := ReducedTypes.mcpuid_M x;
    riscv.mcpuid_S := ReducedTypes.mcpuid_S x;
    riscv.mcpuid_U := ReducedTypes.mcpuid_U x;
    riscv.mcpuid_mcpuid'rst := ReducedTypes.mcpuid_mcpuid'rst x |}.
Definition embedmimpid (x : ReducedTypes.mimpid) : riscv.mimpid :=
 {| riscv.mimpid_RVImpl := ReducedTypes.mimpid_RVImpl x;
    riscv.mimpid_RVSource := ReducedTypes.mimpid_RVSource x |}.
Definition embedmstatus (x : ReducedTypes.mstatus) : riscv.mstatus :=
 {| riscv.mstatus_MFS := ReducedTypes.mstatus_MFS x;
    riscv.mstatus_MIE := ReducedTypes.mstatus_MIE x;
    riscv.mstatus_MIE1 := ReducedTypes.mstatus_MIE1 x;
    riscv.mstatus_MIE2 := ReducedTypes.mstatus_MIE2 x;
    riscv.mstatus_MIE3 := ReducedTypes.mstatus_MIE3 x;
    riscv.mstatus_MMPRV := ReducedTypes.mstatus_MMPRV x;
    riscv.mstatus_MPRV := ReducedTypes.mstatus_MPRV x;
    riscv.mstatus_MPRV1 := ReducedTypes.mstatus_MPRV1 x;
    riscv.mstatus_MPRV2 := ReducedTypes.mstatus_MPRV2 x;
    riscv.mstatus_MPRV3 := ReducedTypes.mstatus_MPRV3 x;
    riscv.mstatus_MSD := ReducedTypes.mstatus_MSD x;
    riscv.mstatus_MXS := ReducedTypes.mstatus_MXS x;
    riscv.mstatus_VM := ReducedTypes.mstatus_VM x;
    riscv.mstatus_mstatus'rst := ReducedTypes.mstatus_mstatus'rst x |}.
Definition embedmtdeleg (x : ReducedTypes.mtdeleg) : riscv.mtdeleg :=
 {| riscv.mtdeleg_Exc_deleg := ReducedTypes.mtdeleg_Exc_deleg x;
    riscv.mtdeleg_Intr_deleg := ReducedTypes.mtdeleg_Intr_deleg x |}.
Definition embedmip (x : ReducedTypes.mip) : riscv.mip :=
 {| riscv.mip_HSIP := ReducedTypes.mip_HSIP x;
    riscv.mip_HTIP := ReducedTypes.mip_HTIP x;
    riscv.mip_MSIP := ReducedTypes.mip_MSIP x;
    riscv.mip_MTIP := ReducedTypes.mip_MTIP x;
    riscv.mip_SSIP := ReducedTypes.mip_SSIP x;
    riscv.mip_STIP := ReducedTypes.mip_STIP x;
    riscv.mip_mip'rst := ReducedTypes.mip_mip'rst x |}.
Definition embedmie (x : ReducedTypes.mie) : riscv.mie :=
 {| riscv.mie_HSIE := ReducedTypes.mie_HSIE x;
    riscv.mie_HTIE := ReducedTypes.mie_HTIE x;
    riscv.mie_MSIE := ReducedTypes.mie_MSIE x;
    riscv.mie_MTIE := ReducedTypes.mie_MTIE x;
    riscv.mie_SSIE := ReducedTypes.mie_SSIE x;
    riscv.mie_STIE := ReducedTypes.mie_STIE x;
    riscv.mie_mie'rst := ReducedTypes.mie_mie'rst x |}.
Definition embedmcause (x : ReducedTypes.mcause) : riscv.mcause :=
 {| riscv.mcause_EC := ReducedTypes.mcause_EC x;
    riscv.mcause_Int := ReducedTypes.mcause_Int x;
    riscv.mcause_mcause'rst := ReducedTypes.mcause_mcause'rst x |}.
Definition embedMachineCSR (x : ReducedTypes.MachineCSR) : riscv.MachineCSR :=
 {| riscv.MachineCSR_mbadaddr := ReducedTypes.MachineCSR_mbadaddr x;
    riscv.MachineCSR_mbase := ReducedTypes.MachineCSR_mbase x;
    riscv.MachineCSR_mbound := ReducedTypes.MachineCSR_mbound x;
    riscv.MachineCSR_mcause := embedmcause (ReducedTypes.MachineCSR_mcause x);
    riscv.MachineCSR_mcpuid := embedmcpuid (ReducedTypes.MachineCSR_mcpuid x);
    riscv.MachineCSR_mdbase := ReducedTypes.MachineCSR_mdbase x;
    riscv.MachineCSR_mdbound := ReducedTypes.MachineCSR_mdbound x;
    riscv.MachineCSR_mepc := ReducedTypes.MachineCSR_mepc x;
    riscv.MachineCSR_mfromhost := ReducedTypes.MachineCSR_mfromhost x;
    riscv.MachineCSR_mhartid := ReducedTypes.MachineCSR_mhartid x;
    riscv.MachineCSR_mibase := ReducedTypes.MachineCSR_mibase x;
    riscv.MachineCSR_mibound := ReducedTypes.MachineCSR_mibound x;
    riscv.MachineCSR_mie := embedmie (ReducedTypes.MachineCSR_mie x);
    riscv.MachineCSR_mimpid := embedmimpid (ReducedTypes.MachineCSR_mimpid x);
    riscv.MachineCSR_mip := embedmip (ReducedTypes.MachineCSR_mip x);
    riscv.MachineCSR_mscratch := ReducedTypes.MachineCSR_mscratch x;
    riscv.MachineCSR_mstatus := embedmstatus (ReducedTypes.MachineCSR_mstatus x);
    riscv.MachineCSR_mtdeleg := embedmtdeleg (ReducedTypes.MachineCSR_mtdeleg x);
    riscv.MachineCSR_mtime_delta := inhabitant _;
    riscv.MachineCSR_mtimecmp := inhabitant _;
    riscv.MachineCSR_mtohost := ReducedTypes.MachineCSR_mtohost x;
    riscv.MachineCSR_mtvec := ReducedTypes.MachineCSR_mtvec x |}.
Definition embedHypervisorCSR (x : ReducedTypes.HypervisorCSR) : riscv.HypervisorCSR :=
 {| riscv.HypervisorCSR_hbadaddr := ReducedTypes.HypervisorCSR_hbadaddr x;
    riscv.HypervisorCSR_hcause := embedmcause (ReducedTypes.HypervisorCSR_hcause x);
    riscv.HypervisorCSR_hepc := ReducedTypes.HypervisorCSR_hepc x;
    riscv.HypervisorCSR_hscratch := ReducedTypes.HypervisorCSR_hscratch x;
    riscv.HypervisorCSR_hstatus := embedmstatus (ReducedTypes.HypervisorCSR_hstatus x);
    riscv.HypervisorCSR_htdeleg := embedmtdeleg (ReducedTypes.HypervisorCSR_htdeleg x);
    riscv.HypervisorCSR_htime_delta := inhabitant _;
    riscv.HypervisorCSR_htimecmp := inhabitant _;
    riscv.HypervisorCSR_htvec := ReducedTypes.HypervisorCSR_htvec x |}.
Definition embedsstatus (x : ReducedTypes.sstatus) : riscv.sstatus :=
 {| riscv.sstatus_SFS := ReducedTypes.sstatus_SFS x;
    riscv.sstatus_SIE := ReducedTypes.sstatus_SIE x;
    riscv.sstatus_SMPRV := ReducedTypes.sstatus_SMPRV x;
    riscv.sstatus_SPIE := ReducedTypes.sstatus_SPIE x;
    riscv.sstatus_SPS := ReducedTypes.sstatus_SPS x;
    riscv.sstatus_SSD := ReducedTypes.sstatus_SSD x;
    riscv.sstatus_SXS := ReducedTypes.sstatus_SXS x;
    riscv.sstatus_sstatus'rst := ReducedTypes.sstatus_sstatus'rst x |}.
Definition embedsip (x : ReducedTypes.sip) : riscv.sip :=
 {| riscv.sip_SSIP := ReducedTypes.sip_SSIP x;
    riscv.sip_STIP := ReducedTypes.sip_STIP x;
    riscv.sip_sip'rst := ReducedTypes.sip_sip'rst x |}.
Definition embedsie (x : ReducedTypes.sie) : riscv.sie :=
 {| riscv.sie_SSIE := ReducedTypes.sie_SSIE x;
    riscv.sie_STIE := ReducedTypes.sie_STIE x;
    riscv.sie_sie'rst := ReducedTypes.sie_sie'rst x |}.
Definition embedSupervisorCSR (x : ReducedTypes.SupervisorCSR) : riscv.SupervisorCSR :=
 {| riscv.SupervisorCSR_sasid := ReducedTypes.SupervisorCSR_sasid x;
    riscv.SupervisorCSR_sbadaddr := ReducedTypes.SupervisorCSR_sbadaddr x;
    riscv.SupervisorCSR_scause := embedmcause (ReducedTypes.SupervisorCSR_scause x);
    riscv.SupervisorCSR_sepc := ReducedTypes.SupervisorCSR_sepc x;
    riscv.SupervisorCSR_sptbr := ReducedTypes.SupervisorCSR_sptbr x;
    riscv.SupervisorCSR_sscratch := ReducedTypes.SupervisorCSR_sscratch x;
    riscv.SupervisorCSR_stime_delta := inhabitant _;
    riscv.SupervisorCSR_stimecmp := inhabitant _;
    riscv.SupervisorCSR_stvec := ReducedTypes.SupervisorCSR_stvec x |}.
Definition embedSynchronousTrap (x : ReducedTypes.SynchronousTrap) : riscv.SynchronousTrap :=
 {| riscv.SynchronousTrap_badaddr := ReducedTypes.SynchronousTrap_badaddr x;
    riscv.SynchronousTrap_trap := embedExceptionType (ReducedTypes.SynchronousTrap_trap x) |}.
Definition embedTransferControl (x : ReducedTypes.TransferControl) : riscv.TransferControl :=
 match x with
 | ReducedTypes.BranchTo value => riscv.BranchTo (value)
 | ReducedTypes.Trap value => riscv.Trap (embedSynchronousTrap (value))
 end.
Definition embedStateDelta (x : ReducedTypes.StateDelta) : riscv.StateDelta :=
 {| riscv.StateDelta_addr := ReducedTypes.StateDelta_addr x;
    riscv.StateDelta_data1 := ReducedTypes.StateDelta_data1 x;
    riscv.StateDelta_data2 := ReducedTypes.StateDelta_data2 x;
    riscv.StateDelta_exc_taken := ReducedTypes.StateDelta_exc_taken x;
    riscv.StateDelta_fetch_exc := ReducedTypes.StateDelta_fetch_exc x;
    riscv.StateDelta_fp_data := inhabitant _;
    riscv.StateDelta_pc := ReducedTypes.StateDelta_pc x;
    riscv.StateDelta_rinstr := embedrawInstType (ReducedTypes.StateDelta_rinstr x);
    riscv.StateDelta_st_width := ReducedTypes.StateDelta_st_width x |}.
Definition embedexception (x : ReducedTypes.exception) : riscv.exception :=
 match x with
 | ReducedTypes.INTERNAL_ERROR value => riscv.INTERNAL_ERROR (value)
 | ReducedTypes.NoException => riscv.NoException
 | ReducedTypes.UNDEFINED value => riscv.UNDEFINED (value)
 end.
Definition embedriscv_state (x : ReducedTypes.riscv_state) : riscv.riscv_state :=
 {| riscv.riscv_state_MEM8 := ReducedTypes.riscv_state_MEM8 x;
    riscv.riscv_state_c_ExitCode := ReducedTypes.riscv_state_c_ExitCode x;
    riscv.riscv_state_c_HCSR := (fun arg0 => embedHypervisorCSR (ReducedTypes.riscv_state_c_HCSR x arg0));
    riscv.riscv_state_c_MCSR := (fun arg0 => embedMachineCSR (ReducedTypes.riscv_state_c_MCSR x arg0));
    riscv.riscv_state_c_NextFetch := (fun arg0 => option_map embedTransferControl (ReducedTypes.riscv_state_c_NextFetch x arg0));
    riscv.riscv_state_c_PC := ReducedTypes.riscv_state_c_PC x;
    riscv.riscv_state_c_ReserveLoad := inhabitant _;
    riscv.riscv_state_c_SCSR := (fun arg0 => embedSupervisorCSR (ReducedTypes.riscv_state_c_SCSR x arg0));
    riscv.riscv_state_c_Skip := ReducedTypes.riscv_state_c_Skip x;
    riscv.riscv_state_c_UCSR := inhabitant _;
    riscv.riscv_state_c_cycles := inhabitant _;
    riscv.riscv_state_c_fpr := inhabitant _;
    riscv.riscv_state_c_gpr := ReducedTypes.riscv_state_c_gpr x;
    riscv.riscv_state_c_instret := inhabitant _;
    riscv.riscv_state_c_tlb := inhabitant _;
    riscv.riscv_state_c_update := (fun arg0 => embedStateDelta (ReducedTypes.riscv_state_c_update x arg0));
    riscv.riscv_state_clock := inhabitant _;
    riscv.riscv_state_done := ReducedTypes.riscv_state_done x;
    riscv.riscv_state_exception := embedexception (ReducedTypes.riscv_state_exception x);
    riscv.riscv_state_log := ReducedTypes.riscv_state_log x;
    riscv.riscv_state_procID := ReducedTypes.riscv_state_procID x;
    riscv.riscv_state_totalCore := ReducedTypes.riscv_state_totalCore x |}.
