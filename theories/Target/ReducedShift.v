(** Original register and immediate shifts; no W variants are introduced. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words bitstring.
From InitE.Target Require Import ReducedTypes ReducedStateOps ReducedMode ReducedUpperJump.
Open Scope N_scope.
Definition dfnSLL '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (state : riscv_state) : riscv_state :=
 let '(v,s) := in32BitMode state in
 let count := if v then w2n (w2w (GPR rs2 s) : word 5) else w2n (w2w (GPR rs2 s) : word 6) in
 writeGPR (word_lsl (GPR rs1 s) count) rd s.
Definition dfnSRL '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (state : riscv_state) : riscv_state :=
 let '(v,s) := in32BitMode state in
 writeGPR (if v then w2w (word_lsr (w2w (GPR rs1 s) : word 32) (w2n (w2w (GPR rs2 s) : word 5)))
 else word_lsr (GPR rs1 s) (w2n (w2w (GPR rs2 s) : word 6))) rd s.
Definition dfnSRA '((rd,(rs1,rs2)) : (word 5*(word 5*word 5))%type) (state : riscv_state) : riscv_state :=
 let '(v,s) := in32BitMode state in
 writeGPR (if v then sw2sw (word_asr (w2w (GPR rs1 s) : word 32) (w2n (w2w (GPR rs2 s) : word 5)))
 else word_asr (GPR rs1 s) (w2n (w2w (GPR rs2 s) : word 6))) rd s.
Definition dfnSLLI '((rd,(rs1,imm)) : (word 5*(word 5*word 6))%type) (state : riscv_state) : riscv_state :=
 let '(v,s) := in32BitMode state in
 if v && fcp_index imm 5 then signalException Illegal_Instr s
 else writeGPR (word_lsl (GPR rs1 s) (w2n imm)) rd s.
Definition dfnSRLI '((rd,(rs1,imm)) : (word 5*(word 5*word 6))%type) (state : riscv_state) : riscv_state :=
 let '(v,s) := in32BitMode state in
 if v && fcp_index imm 5 then signalException Illegal_Instr s else
 let '(v1,s1) := in32BitMode s in
 writeGPR (word_lsr (if v1 then w2w (w2w (GPR rs1 s1) : word 32) else GPR rs1 s1) (w2n imm)) rd s1.
Definition dfnSRAI '((rd,(rs1,imm)) : (word 5*(word 5*word 6))%type) (state : riscv_state) : riscv_state :=
 let '(v,s) := in32BitMode state in
 if v && fcp_index imm 5 then signalException Illegal_Instr s else
 let '(v1,s1) := in32BitMode s in
 writeGPR (word_asr (if v1 then sw2sw (w2w (GPR rs1 s1) : word 32) else GPR rs1 s1) (w2n imm)) rd s1.
