(** Original Divide.lean: signed truncation and explicit zero divisors. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.Target Require Import ReducedTypes ReducedStateOps ReducedMode.
Open Scope N_scope.
Definition dfnREMU '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (s : riscv_state) : riscv_state :=
 writeGPR (if bool_decide (GPR rs2 s = n2w 0) then GPR rs1 s else word_mod (GPR rs1 s) (GPR rs2 s)) rd s.
Definition dfnREM '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (s : riscv_state) : riscv_state :=
 writeGPR (if bool_decide (GPR rs2 s = n2w 0) then GPR rs1 s else word_rem (GPR rs1 s) (GPR rs2 s)) rd s.
Definition dfnDIV '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (s : riscv_state) : riscv_state :=
 writeGPR (if bool_decide (GPR rs2 s = n2w 0) then sw2sw (n2w 1 : word 1)
 else word_quot (GPR rs1 s) (GPR rs2 s)) rd s.
Definition dfnDIVU '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (state : riscv_state) : riscv_state :=
 let '(v,s) := in32BitMode state in let '(v0,s0) := in32BitMode s in
 let divisor : word 64 := if v0 then w2w (w2w (GPR rs2 s0) : word 32) else GPR rs2 s0 in
 writeGPR (if bool_decide (divisor = n2w 0) then sw2sw (n2w 1 : word 1) else
 word_div (if v then w2w (w2w (GPR rs1 s) : word 32) else GPR rs1 s) divisor) rd s0.
