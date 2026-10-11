(** Original IntegerLoad.lean: all translated-state and fault branches retained. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.Target Require Import ReducedTypes ReducedStateOps ReducedMode ReducedUpperJump ReducedMemory.
Open Scope N_scope.
Definition loadAt (rd rs1 : word 5) (offs : word 12) (extend : word 64 -> word 64)
 (s : riscv_state) : riscv_state :=
 let virtual := word_add (GPR rs1 s) (sw2sw offs) in
 let '(address,t) := translateAddr (virtual,(Data,Read)) s in
 match address with
 | None => signalAddressException Load_Fault virtual t
 | Some physical => writeGPR (extend (rawReadData physical t)) rd t
 end.
Definition dfnLB '((rd,(rs1,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let s := state in
 loadAt rd rs1 offs (fun value => sw2sw (w2w value : word 8)) s.
Definition dfnLBU '((rd,(rs1,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let s := state in
 loadAt rd rs1 offs (fun value => w2w (w2w value : word 8)) s.
Definition dfnLH '((rd,(rs1,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let s := state in
 loadAt rd rs1 offs (fun value => sw2sw (w2w value : word 16)) s.
Definition dfnLHU '((rd,(rs1,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let s := state in
 loadAt rd rs1 offs (fun value => w2w (w2w value : word 16)) s.
Definition dfnLW '((rd,(rs1,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let s := state in
 loadAt rd rs1 offs (fun value => sw2sw (w2w value : word 32)) s.
Definition dfnLWU '((rd,(rs1,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let '(mode,s) := in32BitMode state in
 if mode then signalException Illegal_Instr s else
 loadAt rd rs1 offs (fun value => w2w (w2w value : word 32)) s.
Definition dfnLD '((rd,(rs1,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let '(mode,s) := in32BitMode state in
 if mode then signalException Illegal_Instr s else
 loadAt rd rs1 offs (fun value => value) s.
