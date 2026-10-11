(** Original InitE/MachineInitialization.lean callback and metadata definitions. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.finite_maps Require Import alist.
From InitE.Target Require Import ReducedTypes.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require lab_to_target.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From InitE.Target Require Import Configuration.
Open Scope N_scope.
Definition machineSetPc (s : riscv_state) (pc : (word 64)) : riscv_state :=
 riscv_state_c_PC_fupd (fun old core =>
  if bool_decide (core = riscv_state_procID s) then pc else old core) s.
Definition machineSetReg (s : riscv_state) (reg : N) (value : (word 64)) : riscv_state :=
 riscv_state_c_gpr_fupd (fun old core r =>
  if bool_decide (core = riscv_state_procID s) && bool_decide (r = n2w reg)
  then value else old core r) s.
Fixpoint writeBytearray (address : (word 64)) (bytes : list (word 8))
 (memory : (word 64) -> (word 8)) : (word 64) -> (word 8) :=
 match bytes with
 | [] => memory
 | b::rest => fun a => if bool_decide (a = address) then b
   else writeBytearray (address+n2w 1)%w rest memory a
 end.
Definition machineExtReturn (s : riscv_state) (bytes : list (word 8)) : riscv_state :=
 machineSetPc (riscv_state_MEM8_fupd (fun memory =>
   writeBytearray (riscv_state_c_gpr s (riscv_state_procID s) (n2w 12)) bytes memory) s)
   (riscv_state_c_gpr s (riscv_state_procID s) (n2w 1)).
Definition MmioInfo : Type := ((word 8) * (asm.addr 64 * (N * (word 64))))%type.
Definition machineMmioReturn (s : riscv_state) (name : ffiname)
 (info : MmioInfo) (bytes : list (word 8)) : riscv_state :=
 machineSetPc (if bool_decide (name = SharedMem MappedRead)
  then machineSetReg s (fst (snd (snd info))) (word_of_bytes false (n2w 0) bytes)
  else s) (snd (snd (snd info))).
Definition machineFfiInterference (names : list ffiname) (info : list (N*MmioInfo))
 (_ : N) (args : N * (list (word 8) * riscv_state)) : riscv_state :=
 match ALOOKUP info (fst args) with
 | Some record => machineMmioReturn (snd (snd args)) (EL (fst args) names) record (fst (snd args))
 | None => machineExtReturn (snd (snd args)) (fst (snd args))
 end.
Definition machineCacheInterference (_ : N) (args : (word 64) * ((word 64) * riscv_state)) : riscv_state :=
 let s := snd (snd args) in machineSetPc s (riscv_state_c_gpr s (riscv_state_procID s) (n2w 1)).
Definition machineMmioInfo (pc : (word 64)) (first : N) (extra : list lab_to_target.shmem_info_num)
 : list (N*MmioInfo) :=
 combine (MAP (fun i => i+first) (COUNT_LIST (LENGTH extra)))
 (MAP (fun rec => (lab_to_target.nbytes rec,
   (asm.Addr (lab_to_target.addr_reg rec) (n2w (lab_to_target.addr_off rec)),
    (lab_to_target.reg rec,(n2w (lab_to_target.exit_pc rec)+pc)%w)))) extra).
Definition challengeMachineConfig (pc : (word 64)) (program shared : (word 64) -> Prop)
 (names : list ffiname) (first : N) (extra : list lab_to_target.shmem_info_num)
 : machine_config 64 riscv_state RiscVProjection :=
 {| prog_addresses := program; shared_addresses := shared;
    ffi_entry_pcs := MAP (fun i => (pc-n2w ((3+i)*lab_to_target.ffi_offset))%w) (COUNT_LIST first) ++
      MAP (fun rec => (pc+n2w (lab_to_target.entry_pc rec))%w) extra;
    ffi_names := names; ptr_reg := 10; len_reg := 11; ptr2_reg := 12; len2_reg := 13;
    ffi_interfer := machineFfiInterference names (machineMmioInfo pc first extra);
    callee_saved_regs := [24;25;26]; next_interfer := fun _ s => s;
    halt_pc := (pc-n2w lab_to_target.ffi_offset)%w;
    ccache_pc := (pc-n2w (2*lab_to_target.ffi_offset))%w;
    ccache_interfer := machineCacheInterference; target := riscvTarget;
    mmio_info := machineMmioInfo pc first extra |}.
Definition mmioRecordValid (pc : (word 64)) (first : N) (extra : list lab_to_target.shmem_info_num)
 (index : N) : bool :=
 match ALOOKUP (machineMmioInfo pc first extra) index with
 | None => false
 | Some info => (fst (snd (snd info)) <? 32) && aligned 2 (snd (snd (snd info)))
 end.
Definition ffiNameBoundaryValid (names : list ffiname) (first : N) : Prop :=
 first <= LENGTH names /\ forall i, i < LENGTH names ->
 match EL i names with ExtCall _ => i < first | SharedMem _ => first <= i end.
