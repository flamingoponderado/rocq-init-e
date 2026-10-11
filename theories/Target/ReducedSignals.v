(** Original SystemSignals.lean and ControlFetch.lean. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.Target Require Import ReducedTypes ReducedStateOps ReducedMode ReducedUpperJump ReducedMemory.
Open Scope N_scope.
Definition privilege (p : word 2) : Privilege :=
 if bool_decide (p = n2w 0) then User else
 if bool_decide (p = n2w 1) then Supervisor else
 if bool_decide (p = n2w 2) then Hypervisor else
 if bool_decide (p = n2w 3) then Machine else ARB.
Definition dfnUnknownInstruction (s : riscv_state) : riscv_state := signalException Illegal_Instr s.
Definition dfnEBREAK (s : riscv_state) : riscv_state := signalException Breakpoint s.
Definition dfnECALL (s : riscv_state) : riscv_state :=
 signalException (match privilege (mstatus_MPRV (MachineCSR_mstatus (MCSR s))) with
 | User => UMode_Env_Call | Supervisor => SMode_Env_Call
 | Hypervisor => HMode_Env_Call | Machine => MMode_Env_Call end) s.
Definition dfnFETCH_FAULT (addr : word 64) (s : riscv_state) : riscv_state := signalAddressException Fetch_Fault addr s.
Definition dfnFETCH_MISALIGNED (addr : word 64) (s : riscv_state) : riscv_state := signalAddressException Fetch_Misaligned addr s.
