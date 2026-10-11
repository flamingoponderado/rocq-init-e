(** Instruction-byte fetch agreement on the reduced state carrier. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From Galette.HOL.examples.l3_machine_code.riscv.step Require riscv_step.
From InitE.Target Require Import ReducedTypes ReducedStateOps ReducedMemory StateEmbedding StateAgreement MemoryAgreement.
Open Scope N_scope.
Theorem raw_instruction_embedding s address :
 let fetched := ReducedMemory.rawReadInst address s in
 riscv.rawReadInst address (embedriscv_state s) =
 (embedrawInstType (fst fetched),embedriscv_state (snd fetched)).
Proof.
 unfold ReducedMemory.rawReadInst,riscv.rawReadInst,riscv.boolify8.
 rewrite memory_embedding; cbn beta iota zeta.
 rewrite !word_bit_index.
 replace (1 <? dimindex 8) with true by reflexivity.
 replace (0 <? dimindex 8) with true by reflexivity.
 cbn [andb].
 destruct (fcp_index (ReducedTypes.riscv_state_MEM8 s address) 1 &&
 fcp_index (ReducedTypes.riscv_state_MEM8 s address) 0).
 all: rewrite <- write_skip_embedding.
 all: rewrite !memory_embedding; cbn beta iota zeta.
 all: unfold ReducedMemory.writeSkip; cbn.
 all: rewrite ?(proj1 WORD_ADD_0); reflexivity.
Qed.

Theorem fetch_embedding s : physical_mode s ->
 let fetched := ReducedMemory.Fetch s in
 riscv_step.Fetch (embedriscv_state s) =
 (embedrawInstType (fst fetched),embedriscv_state (snd fetched)).
Proof.
 intros H; unfold ReducedMemory.Fetch,ReducedMemory.translateAddr,riscv_step.Fetch.
 rewrite translate_physical by exact H.
 cbn beta iota zeta.
 change (riscv.rawReadInst (ReducedUpperJump.PC s) (embedriscv_state s) =
 (embedrawInstType (fst (ReducedMemory.rawReadInst (ReducedUpperJump.PC s) s)),
 embedriscv_state (snd (ReducedMemory.rawReadInst (ReducedUpperJump.PC s) s)))).
 apply raw_instruction_embedding.
Qed.

Theorem fetch_preserves_validity s :
 Configuration.riscvOk (snd (ReducedMemory.Fetch s)) = Configuration.riscvOk s.
Proof.
 unfold ReducedMemory.Fetch,ReducedMemory.translateAddr,ReducedMemory.rawReadInst.
 cbn [fst].
 destruct (fcp_index (ReducedTypes.riscv_state_MEM8 s (ReducedUpperJump.PC s)) 1 &&
 fcp_index (ReducedTypes.riscv_state_MEM8 s (ReducedUpperJump.PC s)) 0); reflexivity.
Qed.
