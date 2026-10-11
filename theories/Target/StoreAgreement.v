(** All four integer stores simulate the Galette machine under the original
    target validity conditions. No alignment or access-success premise. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From InitE.Target Require Import ReducedTypes ReducedStore ReducedMemory
 Configuration StateEmbedding StateAgreement MemoryAgreement MemoryWriteAgreement.
Open Scope N_scope.

Theorem simulate_SB s (rs1 rs2 : word 5) (offs : word 12) :
 Configuration.riscvOk s = true ->
 embedriscv_state (ReducedStore.dfnSB (rs1,(rs2,offs)) s) =
 riscv.dfn'SB (rs1,rs2,offs) (embedriscv_state s).
Proof.
 intros H; unfold ReducedStore.dfnSB,riscv.dfn'SB.
 unfold ReducedStore.storeAt,ReducedMemory.translateAddr.
 rewrite translate_physical by (apply validity_physical_mode; exact H).
 cbn beta iota zeta.
 rewrite !gpr_embedding.
 apply raw_write_embedding.
Qed.

Theorem simulate_SH s (rs1 rs2 : word 5) (offs : word 12) :
 Configuration.riscvOk s = true ->
 embedriscv_state (ReducedStore.dfnSH (rs1,(rs2,offs)) s) =
 riscv.dfn'SH (rs1,rs2,offs) (embedriscv_state s).
Proof.
 intros H; unfold ReducedStore.dfnSH,riscv.dfn'SH.
 unfold ReducedStore.storeAt,ReducedMemory.translateAddr.
 rewrite translate_physical by (apply validity_physical_mode; exact H).
 cbn beta iota zeta.
 rewrite !gpr_embedding.
 apply raw_write_embedding.
Qed.

Theorem simulate_SW s (rs1 rs2 : word 5) (offs : word 12) :
 Configuration.riscvOk s = true ->
 embedriscv_state (ReducedStore.dfnSW (rs1,(rs2,offs)) s) =
 riscv.dfn'SW (rs1,rs2,offs) (embedriscv_state s).
Proof.
 intros H; unfold ReducedStore.dfnSW,riscv.dfn'SW.
 unfold ReducedStore.storeAt,ReducedMemory.translateAddr.
 rewrite translate_physical by (apply validity_physical_mode; exact H).
 cbn beta iota zeta.
 rewrite !gpr_embedding.
 apply raw_write_embedding.
Qed.

Theorem simulate_SD s (rs1 rs2 : word 5) (offs : word 12) :
 Configuration.riscvOk s = true ->
 embedriscv_state (ReducedStore.dfnSD (rs1,(rs2,offs)) s) =
 riscv.dfn'SD (rs1,rs2,offs) (embedriscv_state s).
Proof.
 intros H; unfold ReducedStore.dfnSD,riscv.dfn'SD.
 rewrite reduced_mode64,full_mode64 by (apply validity_native64; exact H).
 cbn beta iota zeta.
 unfold ReducedStore.storeAt,ReducedMemory.translateAddr.
 rewrite translate_physical by (apply validity_physical_mode; exact H).
 cbn beta iota zeta.
 rewrite !gpr_embedding.
 apply raw_write_embedding.
Qed.
