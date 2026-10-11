(** Original ConditionalBranch.lean; both mode-returned states are retained. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words bitstring.
From InitE.Target Require Import ReducedTypes ReducedStateOps ReducedMode ReducedUpperJump.
Open Scope N_scope.
Definition branchOperands (rs1 rs2 : word 5) (state : riscv_state)
 : word 64*(word 64*riscv_state) :=
 let '(v,s) := in32BitMode state in
 let '(v0,s0) := in32BitMode s in
 ((if v then sw2sw (w2w (GPR rs1 s) : word 32) else GPR rs1 s),
 ((if v0 then sw2sw (w2w (GPR rs2 s0) : word 32) else GPR rs2 s0),s0)).
Definition dfnBEQ '((rs1,(rs2,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let '(a,(b,s)) := branchOperands rs1 rs2 state in
 if bool_decide (a = b) then branchTo (word_add (PC s) (word_lsl (sw2sw offs) 1)) s else s.
Definition dfnBNE '((rs1,(rs2,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let '(a,(b,s)) := branchOperands rs1 rs2 state in
 if negb (bool_decide (a = b)) then branchTo (word_add (PC s) (word_lsl (sw2sw offs) 1)) s else s.
Definition dfnBLTU '((rs1,(rs2,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let '(a,(b,s)) := branchOperands rs1 rs2 state in
 if word_lo a b then branchTo (word_add (PC s) (word_lsl (sw2sw offs) 1)) s else s.
Definition dfnBGEU '((rs1,(rs2,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let '(a,(b,s)) := branchOperands rs1 rs2 state in
 if negb (word_lo a b) then branchTo (word_add (PC s) (word_lsl (sw2sw offs) 1)) s else s.
Definition dfnBLT '((rs1,(rs2,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let '(a,(b,s)) := branchOperands rs1 rs2 state in
 if word_lt a b then branchTo (word_add (PC s) (word_lsl (sw2sw offs) 1)) s else s.
Definition dfnBGE '((rs1,(rs2,offs)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let '(a,(b,s)) := branchOperands rs1 rs2 state in
 if word_le b a then branchTo (word_add (PC s) (word_lsl (sw2sw offs) 1)) s else s.
