(** Original IntegerStore.lean: SD alone applies the original mode guard. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.Target Require Import ReducedTypes ReducedStateOps ReducedMode ReducedUpperJump ReducedMemory.
Open Scope N_scope.
Definition storeAt (rs1 rs2 : word 5) (offs : word 12) (width : N) (s : riscv_state) : riscv_state :=
 let virtual := word_add (GPR rs1 s) (sw2sw offs) in
 let '(address,t) := translateAddr (virtual,(Data,Write)) s in
 match address with
 | None => signalAddressException Store_AMO_Fault virtual t
 | Some physical => rawWriteData physical (GPR rs2 t) width t
 end.
Definition dfnSB '((rs1,(rs2,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let s := state in
 storeAt rs1 rs2 offs 1 s.
Definition dfnSH '((rs1,(rs2,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let s := state in
 storeAt rs1 rs2 offs 2 s.
Definition dfnSW '((rs1,(rs2,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let s := state in
 storeAt rs1 rs2 offs 4 s.
Definition dfnSD '((rs1,(rs2,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let '(mode,s) := in32BitMode state in
 if mode then signalException Illegal_Instr s else
 storeAt rs1 rs2 offs 8 s.
