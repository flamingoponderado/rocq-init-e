(** Original SetLess.lean including RV32 SLTU/SLTIU extension asymmetry. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words bitstring.
From InitE.Target Require Import ReducedTypes ReducedStateOps ReducedMode ReducedUpperJump.
Open Scope N_scope.
Definition dfnSLT '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (state : riscv_state) : riscv_state :=
 let '(v,s) := in32BitMode state in let '(v0,s0) := in32BitMode s in
 let a : word 64 := if v then sw2sw (w2w (GPR rs1 s) : word 32) else GPR rs1 s in
 let b : word 64 := if v0 then sw2sw (w2w (GPR rs2 s0) : word 32) else GPR rs2 s0 in
 writeGPR (v2w [word_lt a b]) rd s0.
Definition dfnSLTU '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (state : riscv_state) : riscv_state :=
 let '(v,s) := in32BitMode state in let '(v0,s0) := in32BitMode s in
 let a : word 64 := if v then w2w (w2w (GPR rs1 s) : word 32) else GPR rs1 s in
 let b : word 64 := if v0 then w2w (w2w (GPR rs2 s0) : word 32) else GPR rs2 s0 in
 writeGPR (v2w [word_lo a b]) rd s0.
Definition dfnSLTI '((rd,(rs1,imm)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let '(v,s) := in32BitMode state in
 let a : word 64 := if v then sw2sw (w2w (GPR rs1 s) : word 32) else GPR rs1 s in
 writeGPR (v2w [word_lt a (sw2sw imm)]) rd s.
Definition dfnSLTIU '((rd,(rs1,imm)) : (word 5*(word 5*word 12))%type) (state : riscv_state) : riscv_state :=
 let '(v,s) := in32BitMode state in
 let a : word 64 := if v then sw2sw (w2w (GPR rs1 s) : word 32) else GPR rs1 s in
 writeGPR (v2w [word_lo a (sw2sw imm)]) rd s.
