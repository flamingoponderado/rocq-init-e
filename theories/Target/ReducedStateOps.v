(** Original L3/Defs.lean integer state operations, on original carriers. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.Target Require Import ReducedTypes.
Open Scope N_scope.
Definition update {A B} `{EqDecision A} (key : A) (value : B) (f : A -> B) : A -> B :=
 fun x => if bool_decide (x = key) then value else f x.
Definition MCSR (s : riscv_state) : MachineCSR := riscv_state_c_MCSR s (riscv_state_procID s).
Definition writeNextFetch (value : option TransferControl) (s : riscv_state) : riscv_state :=
 riscv_state_c_NextFetch_fupd (fun old => update (riscv_state_procID s) value old) s.
Definition setTrap (e : ExceptionType) (badaddr : option (word 64)) (s : riscv_state) : riscv_state :=
 writeNextFetch (Some (Trap {| SynchronousTrap_badaddr := badaddr; SynchronousTrap_trap := e |})) s.
Definition signalException (e : ExceptionType) (s : riscv_state) : riscv_state := setTrap e None s.
Definition gpr (n : word 5) (s : riscv_state) : word 64 :=
 riscv_state_c_gpr s (riscv_state_procID s) n.
Definition GPR (n : word 5) (s : riscv_state) : word 64 :=
 if bool_decide (n = n2w 0) then n2w 0 else gpr n s.
Definition Delta (s : riscv_state) : StateDelta := riscv_state_c_update s (riscv_state_procID s).
Definition writeDelta (value : StateDelta) (s : riscv_state) : riscv_state :=
 riscv_state_c_update_fupd (fun old => update (riscv_state_procID s) value old) s.
Definition writeGpr (value : word 64) (n : word 5) (s : riscv_state) : riscv_state :=
 riscv_state_c_gpr_fupd (fun old => update (riscv_state_procID s)
  (update n value (old (riscv_state_procID s))) old) s.
Definition writeGPR (value : word 64) (n : word 5) (s : riscv_state) : riscv_state :=
 if negb (bool_decide (n = n2w 0)) then writeGpr value n s else s.
Definition NextFetch (s : riscv_state) : option TransferControl :=
 riscv_state_c_NextFetch s (riscv_state_procID s).
Definition ext_status (e : ExtStatus) : word 2 :=
 match e with Off => n2w 0 | Initial => n2w 1 | Clean => n2w 2 | Dirty => n2w 3 end.
Example register_zero_reads_zero s : GPR (n2w 0) s = n2w 0.
Proof. reflexivity. Qed.
Example register_zero_write_suppressed value s : writeGPR value (n2w 0) s = s.
Proof. reflexivity. Qed.
