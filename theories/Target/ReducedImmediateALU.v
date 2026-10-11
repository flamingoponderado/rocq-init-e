(** Original L3/Defs/ImmediateALU.lean: all immediates sign extend to 64. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.Target Require Import ReducedTypes ReducedStateOps.
Open Scope N_scope.
Definition dfnXORI '((rd,(rs1,imm)) : (word 5*(word 5*word 12))%type) (s : riscv_state) : riscv_state :=
 writeGPR (word_xor (GPR rs1 s) (sw2sw imm)) rd s.
Definition dfnORI '((rd,(rs1,imm)) : (word 5*(word 5*word 12))%type) (s : riscv_state) : riscv_state :=
 writeGPR (word_or (GPR rs1 s) (sw2sw imm)) rd s.
Definition dfnANDI '((rd,(rs1,imm)) : (word 5*(word 5*word 12))%type) (s : riscv_state) : riscv_state :=
 writeGPR (word_and (GPR rs1 s) (sw2sw imm)) rd s.
Definition dfnADDI '((rd,(rs1,imm)) : (word 5*(word 5*word 12))%type) (s : riscv_state) : riscv_state :=
 writeGPR (word_add (GPR rs1 s) (sw2sw imm)) rd s.
