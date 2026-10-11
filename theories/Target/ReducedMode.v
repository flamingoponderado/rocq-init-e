(** Original IntegerLoadMode.lean and MMU/Exception.lean. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.string Require Import string ASCIInumbers.
From InitE.Target Require Import ReducedTypes ReducedStateOps.
Open Scope N_scope.
Open Scope hol_string_scope.
Definition raiseException {A} `{Inhabited A} (e : exception) (s : riscv_state) : A*riscv_state :=
 (ARB, if bool_decide (riscv_state_exception s = NoException)
  then riscv_state_exception_fupd (fun _ => e) s else s).
Definition architecture (ab : word 2) (s : riscv_state) : Architecture*riscv_state :=
 if bool_decide (ab = n2w 0) then (RV32I,s) else
 if bool_decide (ab = n2w 2) then (RV64I,s) else
 if bool_decide (ab = n2w 3) then (RV128I,s) else
 raiseException (UNDEFINED ("Unknown architecture: " ++ num_to_dec_string (w2n ab))) s.
Definition curArch (s : riscv_state) : Architecture*riscv_state :=
 architecture (mcpuid_ArchBase (MachineCSR_mcpuid (MCSR s))) s.
Definition in32BitMode (s : riscv_state) : bool*riscv_state :=
 let '(arch,s) := curArch s in (bool_decide (arch = RV32I),s).
Definition dfnADDIW '((rd,(rs1,imm)) : (word 5*(word 5*word 12))%type) (s : riscv_state) : riscv_state :=
 let '(mode,s) := in32BitMode s in
 if mode then signalException Illegal_Instr s else
 writeGPR (sw2sw (w2w (word_add (GPR rs1 s) (sw2sw imm)) : word 32)) rd s.
