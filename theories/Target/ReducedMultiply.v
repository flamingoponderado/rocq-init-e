(** Original Multiply.lean: high products retain all three mode checks. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.Target Require Import ReducedTypes ReducedStateOps ReducedMode.
Open Scope N_scope.
Definition dfnMUL '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (s : riscv_state) : riscv_state :=
 writeGPR (word_mul (GPR rs1 s) (GPR rs2 s)) rd s.
Definition dfnMULHU '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (state : riscv_state) : riscv_state :=
 let '(v,s) := in32BitMode state in let '(v0,s0) := in32BitMode s in
 let a : word 128 := if v then w2w (w2w (GPR rs1 s) : word 32) else w2w (GPR rs1 s) in
 let b : word 128 := if v0 then w2w (w2w (GPR rs2 s0) : word 32) else w2w (GPR rs2 s0) in
 let prod := word_mul a b in
 let '(v1,s1) := in32BitMode s0 in
 writeGPR (if v1 then w2w (w2w (word_lsr prod 32) : word 32)
 else w2w (word_lsr prod 64)) rd s1.
Definition dfnMULHSU '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (state : riscv_state) : riscv_state :=
 let '(v,s) := in32BitMode state in let '(v0,s0) := in32BitMode s in
 let a : word 128 := if v then sw2sw (w2w (GPR rs1 s) : word 32) else sw2sw (GPR rs1 s) in
 let b : word 128 := if v0 then w2w (w2w (GPR rs2 s0) : word 32) else w2w (GPR rs2 s0) in
 let prod := word_mul a b in
 let '(v1,s1) := in32BitMode s0 in
 writeGPR (if v1 then sw2sw (w2w (word_lsr prod 32) : word 32)
 else w2w (word_lsr prod 64)) rd s1.
Definition dfnMULH '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (state : riscv_state) : riscv_state :=
 let '(v,s) := in32BitMode state in let '(v0,s0) := in32BitMode s in
 let a : word 128 := sw2sw (if v then sw2sw (w2w (GPR rs1 s) : word 32) else GPR rs1 s : word 64) in
 let b : word 128 := sw2sw (if v0 then sw2sw (w2w (GPR rs2 s0) : word 32) else GPR rs2 s0 : word 64) in
 let prod := word_mul a b in
 let '(v1,s1) := in32BitMode s0 in
 writeGPR (if v1 then sw2sw (w2w (word_lsr prod 32) : word 32)
 else sw2sw (w2w (word_lsr prod 64) : word 64)) rd s1.
