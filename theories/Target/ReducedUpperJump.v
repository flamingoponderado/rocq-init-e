(** Original UpperJump.lean: bit0 test and original JALR mask are retained. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.Target Require Import ReducedTypes ReducedStateOps.
Open Scope N_scope.
Definition PC (s : riscv_state) : word 64 := riscv_state_c_PC s (riscv_state_procID s).
Definition Skip (s : riscv_state) : word 64 := riscv_state_c_Skip s (riscv_state_procID s).
Definition signalAddressException (e : ExceptionType) (address : word 64) (s : riscv_state) : riscv_state :=
 setTrap e (Some address) s.
Definition branchTo (newPC : word 64) (s : riscv_state) : riscv_state :=
 writeNextFetch (Some (BranchTo newPC)) s.
Definition dfnJALR '((rd,(rs1,imm)) : (word 5*(word 5*word 12))%type) (s : riscv_state) : riscv_state :=
 let v := word_and (word_add (GPR rs1 s) (sw2sw imm)) (sw2sw (n2w 2 : word 2)) in
 if fcp_index v 0 then signalAddressException Fetch_Misaligned v s
 else branchTo v (writeGPR (word_add (PC s) (Skip s)) rd s).
Definition dfnJAL '((rd,imm) : (word 5*word 20)%type) (s : riscv_state) : riscv_state :=
 let v := word_add (PC s) (word_lsl (sw2sw imm) 1) in
 if fcp_index v 0 then signalAddressException Fetch_Misaligned v s
 else branchTo v (writeGPR (word_add (PC s) (Skip s)) rd s).
Definition dfnLUI '((rd,imm) : (word 5*word 20)%type) (s : riscv_state) : riscv_state :=
 writeGPR (sw2sw (word_concat imm (n2w 0 : word 12) : word 32)) rd s.
Definition dfnAUIPC '((rd,imm) : (word 5*word 20)%type) (s : riscv_state) : riscv_state :=
 writeGPR (word_add (PC s) (sw2sw (word_concat imm (n2w 0 : word 12) : word 32))) rd s.
