(** Regression tests on the actual reduced interpreter and state carrier. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.Target Require Import ReducedTypes ReducedStateOps ReducedMode
 ReducedMemory ReducedStep ReducedDivide ReducedMultiply.
Open Scope N_scope.
Definition testState : riscv_state :=
 riscv_state_exception_fupd (fun _ => NoException)
 (riscv_state_c_MCSR_fupd (fun _ _ =>
   MachineCSR_mcpuid_fupd (fun _ => mcpuid_ArchBase_fupd (fun _ => n2w 2) (inhabitant _))
   (inhabitant _)) (inhabitant _)).
Definition nopState := riscv_state_MEM8_fupd
 (fun _ a => if w2n a =? 0 then n2w 19 else n2w 0) testState.
Example nop_advances_four :
 option_map (fun s => w2n (riscv_state_c_PC s (n2w 0))) (ReducedStep.NextRISCV nopState) = Some 4.
Proof. vm_compute; reflexivity. Qed.
Example zero_encoding_fails : ReducedStep.NextRISCV testState = None.
Proof. vm_compute; reflexivity. Qed.
Example physical_translation_ignores_retained_vm_value s a :
 translateAddr (a,(Data,Read)) s = (Some a,s).
Proof. reflexivity. Qed.
Definition crossWordStore := rawWriteData (n2w 5) (n2w 287454020) 4 testState.
Example crossing_store_bytes :
 map (fun i => w2n (riscv_state_MEM8 crossWordStore (n2w i))) [4;5;6;7;8;9] = [0;68;51;34;17;0].
Proof. vm_compute; reflexivity. Qed.
Example div_zero_all_ones :
 w2n (GPR (n2w 1) (dfnDIV (n2w 1,(n2w 0,n2w 0)) testState)) = 18446744073709551615.
Proof. vm_compute; reflexivity. Qed.
Example multiply_alias_reads_old_operands :
 w2n (GPR (n2w 1) (dfnMUL (n2w 1,(n2w 1,n2w 1)) (writeGPR (n2w 3) (n2w 1) testState))) = 9.
Proof. vm_compute; reflexivity. Qed.
