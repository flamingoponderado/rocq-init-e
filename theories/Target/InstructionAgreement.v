(** Instruction simulation on the original reduced carrier. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import fcp_defs lemmas.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From InitE.Target Require Import ReducedTypes ReducedStateOps StateEmbedding StateAgreement
 ReducedRegisterALU ReducedImmediateALU ReducedMultiply ReducedDivide ReducedMode ReducedShift ReducedSetLess ReducedUpperJump ReducedBranch.
Open Scope N_scope.
Theorem simulate_ADD (s : ReducedTypes.riscv_state) (rd rs1 rs2 : word 5) :
 embedriscv_state (dfnADD (rd,(rs1,rs2)) s) =
 riscv.dfn'ADD (rd,rs1,rs2) (embedriscv_state s).
Proof.
 unfold dfnADD,riscv.dfn'ADD.
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding; reflexivity.
Qed.
Theorem simulate_SUB (s : ReducedTypes.riscv_state) (rd rs1 rs2 : word 5) :
 embedriscv_state (dfnSUB (rd,(rs1,rs2)) s) =
 riscv.dfn'SUB (rd,rs1,rs2) (embedriscv_state s).
Proof.
 unfold dfnSUB,riscv.dfn'SUB.
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding; reflexivity.
Qed.
Theorem simulate_AND (s : ReducedTypes.riscv_state) (rd rs1 rs2 : word 5) :
 embedriscv_state (dfnAND (rd,(rs1,rs2)) s) =
 riscv.dfn'AND (rd,rs1,rs2) (embedriscv_state s).
Proof.
 unfold dfnAND,riscv.dfn'AND.
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding; reflexivity.
Qed.
Theorem simulate_OR (s : ReducedTypes.riscv_state) (rd rs1 rs2 : word 5) :
 embedriscv_state (dfnOR (rd,(rs1,rs2)) s) =
 riscv.dfn'OR (rd,rs1,rs2) (embedriscv_state s).
Proof.
 unfold dfnOR,riscv.dfn'OR.
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding; reflexivity.
Qed.
Theorem simulate_XOR (s : ReducedTypes.riscv_state) (rd rs1 rs2 : word 5) :
 embedriscv_state (dfnXOR (rd,(rs1,rs2)) s) =
 riscv.dfn'XOR (rd,rs1,rs2) (embedriscv_state s).
Proof.
 unfold dfnXOR,riscv.dfn'XOR.
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding; reflexivity.
Qed.
Theorem simulate_MUL (s : ReducedTypes.riscv_state) (rd rs1 rs2 : word 5) :
 embedriscv_state (dfnMUL (rd,(rs1,rs2)) s) =
 riscv.dfn'MUL (rd,rs1,rs2) (embedriscv_state s).
Proof.
 unfold dfnMUL,riscv.dfn'MUL.
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding; reflexivity.
Qed.
Theorem simulate_DIV (s : ReducedTypes.riscv_state) (rd rs1 rs2 : word 5) :
 embedriscv_state (dfnDIV (rd,(rs1,rs2)) s) =
 riscv.dfn'DIV (rd,rs1,rs2) (embedriscv_state s).
Proof.
 unfold dfnDIV,riscv.dfn'DIV.
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding; reflexivity.
Qed.
Theorem simulate_REM (s : ReducedTypes.riscv_state) (rd rs1 rs2 : word 5) :
 embedriscv_state (dfnREM (rd,(rs1,rs2)) s) =
 riscv.dfn'REM (rd,rs1,rs2) (embedriscv_state s).
Proof.
 unfold dfnREM,riscv.dfn'REM.
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding; reflexivity.
Qed.
Theorem simulate_REMU (s : ReducedTypes.riscv_state) (rd rs1 rs2 : word 5) :
 embedriscv_state (dfnREMU (rd,(rs1,rs2)) s) =
 riscv.dfn'REMU (rd,rs1,rs2) (embedriscv_state s).
Proof.
 unfold dfnREMU,riscv.dfn'REMU.
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding; reflexivity.
Qed.
Theorem simulate_ADDI (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (imm : word 12) :
 embedriscv_state (dfnADDI (rd,(rs1,imm)) s) =
 riscv.dfn'ADDI (rd,rs1,imm) (embedriscv_state s).
Proof.
 unfold dfnADDI,riscv.dfn'ADDI.
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding; reflexivity.
Qed.
Theorem simulate_ANDI (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (imm : word 12) :
 embedriscv_state (dfnANDI (rd,(rs1,imm)) s) =
 riscv.dfn'ANDI (rd,rs1,imm) (embedriscv_state s).
Proof.
 unfold dfnANDI,riscv.dfn'ANDI.
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding; reflexivity.
Qed.
Theorem simulate_ORI (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (imm : word 12) :
 embedriscv_state (dfnORI (rd,(rs1,imm)) s) =
 riscv.dfn'ORI (rd,rs1,imm) (embedriscv_state s).
Proof.
 unfold dfnORI,riscv.dfn'ORI.
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding; reflexivity.
Qed.
Theorem simulate_XORI (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (imm : word 12) :
 embedriscv_state (dfnXORI (rd,(rs1,imm)) s) =
 riscv.dfn'XORI (rd,rs1,imm) (embedriscv_state s).
Proof.
 unfold dfnXORI,riscv.dfn'XORI.
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding; reflexivity.
Qed.
Lemma low_extract_resize {a b : N} (w : word a) :
 (word_extract (dimindex b-1) 0 w : word b) = w2w w.
Proof. unfold word_extract; rewrite <- w2w_w2w; rewrite w2w_id; reflexivity. Qed.
Lemma widened_value {a b : N} (w : word a) :
 dimindex a <= dimindex b -> w2n (w2w w : word b) = w2n w.
Proof.
 intros H; rewrite w2n_w2w.
 assert (HE : (dimindex a <=? dimindex b) = true) by (apply N.leb_le; exact H).
 rewrite HE; reflexivity.
Qed.
Theorem simulate_DIVU_64 (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (rs2 : word 5) :
 native64 s -> embedriscv_state (dfnDIVU (rd,(rs1,rs2)) s) =
 riscv.dfn'DIVU (rd,rs1,rs2) (embedriscv_state s).
Proof.
 intros H; unfold dfnDIVU,riscv.dfn'DIVU.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta.
 cbn [andb negb].
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding.
 all: try reflexivity.
 all: unfold word_lsl_bv,word_lsr_bv,word_asr_bv.
 all: change (5%N) with (dimindex 6-1)%N.
 all: try change (31%N) with (dimindex 32-1)%N.
 all: try rewrite low_extract_resize.
 all: try rewrite (widened_value (a:=6) (b:=64)) by (vm_compute; congruence).
 all: reflexivity.
Qed.
Theorem simulate_SLL_64 (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (rs2 : word 5) :
 native64 s -> embedriscv_state (dfnSLL (rd,(rs1,rs2)) s) =
 riscv.dfn'SLL (rd,rs1,rs2) (embedriscv_state s).
Proof.
 intros H; unfold dfnSLL,riscv.dfn'SLL.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta.
 cbn [andb negb].
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding.
 all: try reflexivity.
 all: unfold word_lsl_bv,word_lsr_bv,word_asr_bv.
 all: change (5%N) with (dimindex 6-1)%N.
 all: try change (31%N) with (dimindex 32-1)%N.
 all: try rewrite low_extract_resize.
 all: try rewrite (widened_value (a:=6) (b:=64)) by (vm_compute; congruence).
 all: reflexivity.
Qed.
Theorem simulate_SRL_64 (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (rs2 : word 5) :
 native64 s -> embedriscv_state (dfnSRL (rd,(rs1,rs2)) s) =
 riscv.dfn'SRL (rd,rs1,rs2) (embedriscv_state s).
Proof.
 intros H; unfold dfnSRL,riscv.dfn'SRL.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta.
 cbn [andb negb].
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding.
 all: try reflexivity.
 all: unfold word_lsl_bv,word_lsr_bv,word_asr_bv.
 all: change (5%N) with (dimindex 6-1)%N.
 all: try change (31%N) with (dimindex 32-1)%N.
 all: try rewrite low_extract_resize.
 all: try rewrite (widened_value (a:=6) (b:=64)) by (vm_compute; congruence).
 all: reflexivity.
Qed.
Theorem simulate_SRA_64 (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (rs2 : word 5) :
 native64 s -> embedriscv_state (dfnSRA (rd,(rs1,rs2)) s) =
 riscv.dfn'SRA (rd,rs1,rs2) (embedriscv_state s).
Proof.
 intros H; unfold dfnSRA,riscv.dfn'SRA.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta.
 cbn [andb negb].
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding.
 all: try reflexivity.
 all: unfold word_lsl_bv,word_lsr_bv,word_asr_bv.
 all: change (5%N) with (dimindex 6-1)%N.
 all: try change (31%N) with (dimindex 32-1)%N.
 all: try rewrite low_extract_resize.
 all: try rewrite (widened_value (a:=6) (b:=64)) by (vm_compute; congruence).
 all: reflexivity.
Qed.
Theorem simulate_SLT_64 (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (rs2 : word 5) :
 native64 s -> embedriscv_state (dfnSLT (rd,(rs1,rs2)) s) =
 riscv.dfn'SLT (rd,rs1,rs2) (embedriscv_state s).
Proof.
 intros H; unfold dfnSLT,riscv.dfn'SLT.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta.
 cbn [andb negb].
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding.
 all: try reflexivity.
 all: unfold word_lsl_bv,word_lsr_bv,word_asr_bv.
 all: change (5%N) with (dimindex 6-1)%N.
 all: try change (31%N) with (dimindex 32-1)%N.
 all: try rewrite low_extract_resize.
 all: try rewrite (widened_value (a:=6) (b:=64)) by (vm_compute; congruence).
 all: reflexivity.
Qed.
Theorem simulate_SLTU_64 (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (rs2 : word 5) :
 native64 s -> embedriscv_state (dfnSLTU (rd,(rs1,rs2)) s) =
 riscv.dfn'SLTU (rd,rs1,rs2) (embedriscv_state s).
Proof.
 intros H; unfold dfnSLTU,riscv.dfn'SLTU.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta.
 cbn [andb negb].
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding.
 all: try reflexivity.
 all: unfold word_lsl_bv,word_lsr_bv,word_asr_bv.
 all: change (5%N) with (dimindex 6-1)%N.
 all: try change (31%N) with (dimindex 32-1)%N.
 all: try rewrite low_extract_resize.
 all: try rewrite (widened_value (a:=6) (b:=64)) by (vm_compute; congruence).
 all: reflexivity.
Qed.
Theorem simulate_SLLI_64 (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (imm : word 6) :
 native64 s -> embedriscv_state (dfnSLLI (rd,(rs1,imm)) s) =
 riscv.dfn'SLLI (rd,rs1,imm) (embedriscv_state s).
Proof.
 intros H; unfold dfnSLLI,riscv.dfn'SLLI.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta.
 cbn [andb negb].
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding.
 all: try reflexivity.
 all: unfold word_lsl_bv,word_lsr_bv,word_asr_bv.
 all: change (5%N) with (dimindex 6-1)%N.
 all: try change (31%N) with (dimindex 32-1)%N.
 all: try rewrite low_extract_resize.
 all: try rewrite (widened_value (a:=6) (b:=64)) by (vm_compute; congruence).
 all: reflexivity.
Qed.
Theorem simulate_SRLI_64 (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (imm : word 6) :
 native64 s -> embedriscv_state (dfnSRLI (rd,(rs1,imm)) s) =
 riscv.dfn'SRLI (rd,rs1,imm) (embedriscv_state s).
Proof.
 intros H; unfold dfnSRLI,riscv.dfn'SRLI.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta.
 cbn [andb negb].
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding.
 all: try reflexivity.
 all: unfold word_lsl_bv,word_lsr_bv,word_asr_bv.
 all: change (5%N) with (dimindex 6-1)%N.
 all: try change (31%N) with (dimindex 32-1)%N.
 all: try rewrite low_extract_resize.
 all: try rewrite (widened_value (a:=6) (b:=64)) by (vm_compute; congruence).
 all: reflexivity.
Qed.
Theorem simulate_SRAI_64 (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (imm : word 6) :
 native64 s -> embedriscv_state (dfnSRAI (rd,(rs1,imm)) s) =
 riscv.dfn'SRAI (rd,rs1,imm) (embedriscv_state s).
Proof.
 intros H; unfold dfnSRAI,riscv.dfn'SRAI.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta.
 cbn [andb negb].
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding.
 all: try reflexivity.
 all: unfold word_lsl_bv,word_lsr_bv,word_asr_bv.
 all: change (5%N) with (dimindex 6-1)%N.
 all: try change (31%N) with (dimindex 32-1)%N.
 all: try rewrite low_extract_resize.
 all: try rewrite (widened_value (a:=6) (b:=64)) by (vm_compute; congruence).
 all: reflexivity.
Qed.
Theorem simulate_SLTI_64 (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (imm : word 12) :
 native64 s -> embedriscv_state (dfnSLTI (rd,(rs1,imm)) s) =
 riscv.dfn'SLTI (rd,rs1,imm) (embedriscv_state s).
Proof.
 intros H; unfold dfnSLTI,riscv.dfn'SLTI.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta.
 cbn [andb negb].
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding.
 all: try reflexivity.
 all: unfold word_lsl_bv,word_lsr_bv,word_asr_bv.
 all: change (5%N) with (dimindex 6-1)%N.
 all: try change (31%N) with (dimindex 32-1)%N.
 all: try rewrite low_extract_resize.
 all: try rewrite (widened_value (a:=6) (b:=64)) by (vm_compute; congruence).
 all: reflexivity.
Qed.
Theorem simulate_SLTIU_64 (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (imm : word 12) :
 native64 s -> embedriscv_state (dfnSLTIU (rd,(rs1,imm)) s) =
 riscv.dfn'SLTIU (rd,rs1,imm) (embedriscv_state s).
Proof.
 intros H; unfold dfnSLTIU,riscv.dfn'SLTIU.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta.
 cbn [andb negb].
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding.
 all: try reflexivity.
 all: unfold word_lsl_bv,word_lsr_bv,word_asr_bv.
 all: change (5%N) with (dimindex 6-1)%N.
 all: try change (31%N) with (dimindex 32-1)%N.
 all: try rewrite low_extract_resize.
 all: try rewrite (widened_value (a:=6) (b:=64)) by (vm_compute; congruence).
 all: reflexivity.
Qed.
Theorem simulate_ADDIW_64 (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (imm : word 12) :
 native64 s -> embedriscv_state (dfnADDIW (rd,(rs1,imm)) s) =
 riscv.dfn'ADDIW (rd,rs1,imm) (embedriscv_state s).
Proof.
 intros H; unfold dfnADDIW,riscv.dfn'ADDIW.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta.
 cbn [andb negb].
 rewrite !gpr_embedding.
 try (match goal with |- context [if ?b then _ else _] => destruct b end).
 all: rewrite <- !write_GPR_embedding.
 all: try reflexivity.
 all: unfold word_lsl_bv,word_lsr_bv,word_asr_bv.
 all: change (5%N) with (dimindex 6-1)%N.
 all: try change (31%N) with (dimindex 32-1)%N.
 all: try rewrite low_extract_resize.
 all: try rewrite (widened_value (a:=6) (b:=64)) by (vm_compute; congruence).
 all: reflexivity.
Qed.

Theorem simulate_MULH_64 (s : ReducedTypes.riscv_state) (rd rs1 rs2 : word 5) :
 native64 s -> embedriscv_state (dfnMULH (rd,(rs1,rs2)) s) =
 riscv.dfn'MULH (rd,rs1,rs2) (embedriscv_state s).
Proof.
 intros H; unfold dfnMULH,riscv.dfn'MULH.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta; rewrite !gpr_embedding.
 rewrite <- !write_GPR_embedding; reflexivity.
Qed.

Theorem simulate_MULHU_64 (s : ReducedTypes.riscv_state) (rd rs1 rs2 : word 5) :
 native64 s -> embedriscv_state (dfnMULHU (rd,(rs1,rs2)) s) =
 riscv.dfn'MULHU (rd,rs1,rs2) (embedriscv_state s).
Proof.
 intros H; unfold dfnMULHU,riscv.dfn'MULHU.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta; rewrite !gpr_embedding.
 rewrite <- !write_GPR_embedding; reflexivity.
Qed.

Theorem simulate_MULHSU_64 (s : ReducedTypes.riscv_state) (rd rs1 rs2 : word 5) :
 native64 s -> embedriscv_state (dfnMULHSU (rd,(rs1,rs2)) s) =
 riscv.dfn'MULHSU (rd,rs1,rs2) (embedriscv_state s).
Proof.
 intros H; unfold dfnMULHSU,riscv.dfn'MULHSU.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta; rewrite !gpr_embedding.
 rewrite <- !write_GPR_embedding; reflexivity.
Qed.

Theorem simulate_LUI (s : ReducedTypes.riscv_state) (rd : word 5) (imm : word 20) :
 embedriscv_state (dfnLUI (rd,imm) s) =
 riscv.dfn'LUI (rd,imm) (embedriscv_state s).
Proof. unfold dfnLUI,riscv.dfn'LUI; rewrite ?pc_embedding; rewrite <- !write_GPR_embedding; reflexivity. Qed.

Theorem simulate_AUIPC (s : ReducedTypes.riscv_state) (rd : word 5) (imm : word 20) :
 embedriscv_state (dfnAUIPC (rd,imm) s) =
 riscv.dfn'AUIPC (rd,imm) (embedriscv_state s).
Proof. unfold dfnAUIPC,riscv.dfn'AUIPC; rewrite ?pc_embedding; rewrite <- !write_GPR_embedding; reflexivity. Qed.

Theorem simulate_BEQ_64 (s : ReducedTypes.riscv_state) (rs1 rs2 : word 5) (offs : word 12) :
 native64 s -> embedriscv_state (dfnBEQ (rs1,(rs2,offs)) s) =
 riscv.dfn'BEQ (rs1,rs2,offs) (embedriscv_state s).
Proof.
 intros H; unfold dfnBEQ,branchOperands,riscv.dfn'BEQ.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta; rewrite !gpr_embedding, ?pc_embedding.
 rewrite ?word_ge_Zs, ?word_le_Zs, ?word_hs_w2n, ?word_lo_w2n.
 try rewrite <- N.leb_antisym.
 match goal with |- context [if ?b then _ else _] => destruct b end.
 all: rewrite ?branch_embedding; reflexivity.
Qed.

Theorem simulate_BNE_64 (s : ReducedTypes.riscv_state) (rs1 rs2 : word 5) (offs : word 12) :
 native64 s -> embedriscv_state (dfnBNE (rs1,(rs2,offs)) s) =
 riscv.dfn'BNE (rs1,rs2,offs) (embedriscv_state s).
Proof.
 intros H; unfold dfnBNE,branchOperands,riscv.dfn'BNE.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta; rewrite !gpr_embedding, ?pc_embedding.
 rewrite ?word_ge_Zs, ?word_le_Zs, ?word_hs_w2n, ?word_lo_w2n.
 try rewrite <- N.leb_antisym.
 match goal with |- context [if ?b then _ else _] => destruct b end.
 all: rewrite ?branch_embedding; reflexivity.
Qed.

Theorem simulate_BLT_64 (s : ReducedTypes.riscv_state) (rs1 rs2 : word 5) (offs : word 12) :
 native64 s -> embedriscv_state (dfnBLT (rs1,(rs2,offs)) s) =
 riscv.dfn'BLT (rs1,rs2,offs) (embedriscv_state s).
Proof.
 intros H; unfold dfnBLT,branchOperands,riscv.dfn'BLT.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta; rewrite !gpr_embedding, ?pc_embedding.
 rewrite ?word_ge_Zs, ?word_le_Zs, ?word_hs_w2n, ?word_lo_w2n.
 try rewrite <- N.leb_antisym.
 match goal with |- context [if ?b then _ else _] => destruct b end.
 all: rewrite ?branch_embedding; reflexivity.
Qed.

Theorem simulate_BLTU_64 (s : ReducedTypes.riscv_state) (rs1 rs2 : word 5) (offs : word 12) :
 native64 s -> embedriscv_state (dfnBLTU (rs1,(rs2,offs)) s) =
 riscv.dfn'BLTU (rs1,rs2,offs) (embedriscv_state s).
Proof.
 intros H; unfold dfnBLTU,branchOperands,riscv.dfn'BLTU.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta; rewrite !gpr_embedding, ?pc_embedding.
 rewrite ?word_ge_Zs, ?word_le_Zs, ?word_hs_w2n, ?word_lo_w2n.
 try rewrite <- N.leb_antisym.
 match goal with |- context [if ?b then _ else _] => destruct b end.
 all: rewrite ?branch_embedding; reflexivity.
Qed.

Theorem simulate_BGE_64 (s : ReducedTypes.riscv_state) (rs1 rs2 : word 5) (offs : word 12) :
 native64 s -> embedriscv_state (dfnBGE (rs1,(rs2,offs)) s) =
 riscv.dfn'BGE (rs1,rs2,offs) (embedriscv_state s).
Proof.
 intros H; unfold dfnBGE,branchOperands,riscv.dfn'BGE.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta; rewrite !gpr_embedding, ?pc_embedding.
 rewrite ?word_ge_Zs, ?word_le_Zs, ?word_hs_w2n, ?word_lo_w2n.
 try rewrite <- N.leb_antisym.
 match goal with |- context [if ?b then _ else _] => destruct b end.
 all: rewrite ?branch_embedding; reflexivity.
Qed.

Theorem simulate_BGEU_64 (s : ReducedTypes.riscv_state) (rs1 rs2 : word 5) (offs : word 12) :
 native64 s -> embedriscv_state (dfnBGEU (rs1,(rs2,offs)) s) =
 riscv.dfn'BGEU (rs1,rs2,offs) (embedriscv_state s).
Proof.
 intros H; unfold dfnBGEU,branchOperands,riscv.dfn'BGEU.
 rewrite !reduced_mode64 by exact H.
 rewrite !full_mode64 by exact H.
 cbn beta iota zeta; rewrite !gpr_embedding, ?pc_embedding.
 rewrite ?word_ge_Zs, ?word_le_Zs, ?word_hs_w2n, ?word_lo_w2n.
 try rewrite <- N.leb_antisym.
 match goal with |- context [if ?b then _ else _] => destruct b end.
 all: rewrite ?branch_embedding; reflexivity.
Qed.

Theorem simulate_JAL (s : ReducedTypes.riscv_state) (rd : word 5) (imm : word 20) :
 embedriscv_state (dfnJAL (rd,imm) s) =
 riscv.dfn'JAL (rd,imm) (embedriscv_state s).
Proof.
 unfold dfnJAL,riscv.dfn'JAL.
 rewrite ?gpr_embedding, !pc_embedding, !skip_embedding, !word_bit_index.
 replace (0 <? dimindex 64) with true by reflexivity.
 cbn [andb].
 unfold ReducedUpperJump.PC.
 match goal with |- context [if ?b then _ else _] => destruct b end.
 - rewrite address_exception_embedding; reflexivity.
 - rewrite branch_embedding, write_GPR_embedding; reflexivity.
Qed.

Theorem simulate_JALR (s : ReducedTypes.riscv_state) (rd rs1 : word 5) (imm : word 12) :
 embedriscv_state (dfnJALR (rd,(rs1,imm)) s) =
 riscv.dfn'JALR (rd,rs1,imm) (embedriscv_state s).
Proof.
 unfold dfnJALR,riscv.dfn'JALR.
 rewrite ?gpr_embedding, !pc_embedding, !skip_embedding, !word_bit_index.
 replace (0 <? dimindex 64) with true by reflexivity.
 cbn [andb].
 unfold ReducedUpperJump.PC.
 match goal with |- context [if ?b then _ else _] => destruct b end.
 - rewrite address_exception_embedding; reflexivity.
 - rewrite branch_embedding, write_GPR_embedding; reflexivity.
Qed.
