(** Original reduced target State.lean, over its exact reduced carrier. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words alignment.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.examples.machine_code.hoare_triple Require set_sep.
From Galette.cakeml.compiler.encoders.asm Require asmProps.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From InitE.Target Require Import ReducedTypes ReducedStep ReferenceChoices.
Open Scope N_scope.
Definition RiscVProjection : Type :=
 (word 5 * (word 2 * (option TransferControl * (exception * ((word 5 -> word 64) *
 ((word 64 * word 8 -> Prop) * word 64))))))%type.
Definition riscvProj (domain : word 64 -> Prop) (s : riscv_state) : RiscVProjection :=
 (mstatus_VM (MachineCSR_mstatus (riscv_state_c_MCSR s (riscv_state_procID s))),
 (mcpuid_ArchBase (MachineCSR_mcpuid (riscv_state_c_MCSR s (riscv_state_procID s))),
 (riscv_state_c_NextFetch s (riscv_state_procID s),
 (riscv_state_exception s,
 (riscv_state_c_gpr s (riscv_state_procID s),
 (set_sep.fun2set (riscv_state_MEM8 s,domain),riscv_state_c_PC s (riscv_state_procID s))))))).
Definition riscvOk (s : riscv_state) : bool :=
 bool_decide (mstatus_VM (MachineCSR_mstatus (riscv_state_c_MCSR s (riscv_state_procID s))) = n2w 0) &&
 bool_decide (mcpuid_ArchBase (MachineCSR_mcpuid (riscv_state_c_MCSR s (riscv_state_procID s))) = n2w 2) &&
 bool_decide (riscv_state_c_NextFetch s (riscv_state_procID s) = None) &&
 bool_decide (riscv_state_exception s = NoException) &&
 aligned 2 (riscv_state_c_PC s (riscv_state_procID s)).
#[local] Instance target_inhabited : Inhabited (asmProps.target 64 riscv_state RiscVProjection) :=
 asmProps.mk_target riscv_target.riscv_config (fun s => s)
 (fun _ => n2w 0) (fun _ _ => n2w 0) (fun _ _ => n2w 0)
 (fun _ _ => n2w 0) (fun _ => true) riscvProj.
Definition riscvNext (s : riscv_state) : riscv_state := referenceThe (ReducedStep.NextRISCV s).
Definition riscvTarget : asmProps.target 64 riscv_state RiscVProjection :=
 asmProps.mk_target riscv_target.riscv_config riscvNext
 (fun s => riscv_state_c_PC s (riscv_state_procID s))
 (fun s r => riscv_state_c_gpr s (riscv_state_procID s) (n2w r))
 (asmProps.get_fp_reg (ARB : asmProps.target 64 riscv_state RiscVProjection))
 riscv_state_MEM8 riscvOk riscvProj.
Example integer_target_only : asm.fp_reg_count (asmProps.config riscvTarget) = 0.
Proof. reflexivity. Qed.
