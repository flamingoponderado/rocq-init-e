(** Load simulations under the original target validity conditions. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From InitE.Target Require Import ReducedTypes ReducedLoad ReducedMemory Configuration StateEmbedding StateAgreement InstructionAgreement MemoryAgreement.
Open Scope N_scope.

Theorem simulate_LB s (rd rs1 : word 5) (offs : word 12) :
 Configuration.riscvOk s = true ->
 embedriscv_state (dfnLB (rd,(rs1,offs)) s) =
 riscv.dfn'LB (rd,rs1,offs) (embedriscv_state s).
Proof.
 intros H; unfold dfnLB,riscv.dfn'LB.
 unfold loadAt,ReducedMemory.translateAddr.
 rewrite translate_physical by (apply validity_physical_mode; exact H).
 cbn beta iota zeta.
 rewrite raw_read_embedding,gpr_embedding.
 change (7%N) with (dimindex 8-1)%N; rewrite low_extract_resize.
 rewrite <- write_GPR_embedding; reflexivity.
Qed.

Theorem simulate_LBU s (rd rs1 : word 5) (offs : word 12) :
 Configuration.riscvOk s = true ->
 embedriscv_state (dfnLBU (rd,(rs1,offs)) s) =
 riscv.dfn'LBU (rd,rs1,offs) (embedriscv_state s).
Proof.
 intros H; unfold dfnLBU,riscv.dfn'LBU.
 unfold loadAt,ReducedMemory.translateAddr.
 rewrite translate_physical by (apply validity_physical_mode; exact H).
 cbn beta iota zeta.
 rewrite raw_read_embedding,gpr_embedding.
 change (7%N) with (dimindex 8-1)%N; rewrite low_extract_resize.
 rewrite <- write_GPR_embedding; reflexivity.
Qed.

Theorem simulate_LH s (rd rs1 : word 5) (offs : word 12) :
 Configuration.riscvOk s = true ->
 embedriscv_state (dfnLH (rd,(rs1,offs)) s) =
 riscv.dfn'LH (rd,rs1,offs) (embedriscv_state s).
Proof.
 intros H; unfold dfnLH,riscv.dfn'LH.
 unfold loadAt,ReducedMemory.translateAddr.
 rewrite translate_physical by (apply validity_physical_mode; exact H).
 cbn beta iota zeta.
 rewrite raw_read_embedding,gpr_embedding.
 change (15%N) with (dimindex 16-1)%N; rewrite low_extract_resize.
 rewrite <- write_GPR_embedding; reflexivity.
Qed.

Theorem simulate_LHU s (rd rs1 : word 5) (offs : word 12) :
 Configuration.riscvOk s = true ->
 embedriscv_state (dfnLHU (rd,(rs1,offs)) s) =
 riscv.dfn'LHU (rd,rs1,offs) (embedriscv_state s).
Proof.
 intros H; unfold dfnLHU,riscv.dfn'LHU.
 unfold loadAt,ReducedMemory.translateAddr.
 rewrite translate_physical by (apply validity_physical_mode; exact H).
 cbn beta iota zeta.
 rewrite raw_read_embedding,gpr_embedding.
 change (15%N) with (dimindex 16-1)%N; rewrite low_extract_resize.
 rewrite <- write_GPR_embedding; reflexivity.
Qed.

Theorem simulate_LW s (rd rs1 : word 5) (offs : word 12) :
 Configuration.riscvOk s = true ->
 embedriscv_state (dfnLW (rd,(rs1,offs)) s) =
 riscv.dfn'LW (rd,rs1,offs) (embedriscv_state s).
Proof.
 intros H; unfold dfnLW,riscv.dfn'LW.
 unfold loadAt,ReducedMemory.translateAddr.
 rewrite translate_physical by (apply validity_physical_mode; exact H).
 cbn beta iota zeta.
 rewrite raw_read_embedding,gpr_embedding.
 change (31%N) with (dimindex 32-1)%N; rewrite low_extract_resize.
 rewrite <- write_GPR_embedding; reflexivity.
Qed.

Theorem simulate_LWU s (rd rs1 : word 5) (offs : word 12) :
 Configuration.riscvOk s = true ->
 embedriscv_state (dfnLWU (rd,(rs1,offs)) s) =
 riscv.dfn'LWU (rd,rs1,offs) (embedriscv_state s).
Proof.
 intros H; unfold dfnLWU,riscv.dfn'LWU.
 rewrite reduced_mode64,full_mode64 by (apply validity_native64; exact H).
 cbn beta iota zeta.
 unfold loadAt,ReducedMemory.translateAddr.
 rewrite translate_physical by (apply validity_physical_mode; exact H).
 cbn beta iota zeta.
 rewrite raw_read_embedding,gpr_embedding.
 change (31%N) with (dimindex 32-1)%N; rewrite low_extract_resize.
 rewrite <- write_GPR_embedding; reflexivity.
Qed.

Theorem simulate_LD s (rd rs1 : word 5) (offs : word 12) :
 Configuration.riscvOk s = true ->
 embedriscv_state (dfnLD (rd,(rs1,offs)) s) =
 riscv.dfn'LD (rd,rs1,offs) (embedriscv_state s).
Proof.
 intros H; unfold dfnLD,riscv.dfn'LD.
 rewrite reduced_mode64,full_mode64 by (apply validity_native64; exact H).
 cbn beta iota zeta.
 unfold loadAt,ReducedMemory.translateAddr.
 rewrite translate_physical by (apply validity_physical_mode; exact H).
 cbn beta iota zeta.
 rewrite raw_read_embedding,gpr_embedding.
 rewrite <- write_GPR_embedding; reflexivity.
Qed.
