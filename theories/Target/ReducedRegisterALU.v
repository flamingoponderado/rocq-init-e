(** Original L3/Defs/RegisterALU.lean. No architecture-mode condition is added. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.Target Require Import ReducedTypes ReducedStateOps.
Open Scope N_scope.
Definition dfnXOR '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (s : riscv_state) : riscv_state :=
 writeGPR (word_xor (GPR rs1 s) (GPR rs2 s)) rd s.
Definition dfnSUB '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (s : riscv_state) : riscv_state :=
 writeGPR (word_sub (GPR rs1 s) (GPR rs2 s)) rd s.
Definition dfnOR '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (s : riscv_state) : riscv_state :=
 writeGPR (word_or (GPR rs1 s) (GPR rs2 s)) rd s.
Definition dfnAND '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (s : riscv_state) : riscv_state :=
 writeGPR (word_and (GPR rs1 s) (GPR rs2 s)) rd s.
Definition dfnADD '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (s : riscv_state) : riscv_state :=
 writeGPR (word_add (GPR rs1 s) (GPR rs2 s)) rd s.
