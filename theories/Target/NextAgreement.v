(** Composition lemmas for the actual reduced outer step. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From Galette.HOL.examples.l3_machine_code.riscv.step Require riscv_step.
From InitE.Target Require Import ReducedTypes ReducedStep StateEmbedding StateAgreement FetchAgreement MemoryAgreement Step.
Theorem update_pc_embedding s pc :
 option_map embedriscv_state (ReducedStep.update_pc pc s) =
 riscv_step.update_pc pc (embedriscv_state s).
Proof.
 unfold ReducedStep.update_pc,riscv_step.update_pc,riscv.write'PC,
 embedriscv_state,ReducedTypes.riscv_state_c_PC_fupd,riscv.riscv_state_c_PC_fupd.
 cbn; rewrite update_agreement; reflexivity.
Qed.
Theorem next_fetch_projection s :
 riscv.NextFetch (embedriscv_state s) = option_map embedTransferControl (ReducedStateOps.NextFetch s).
Proof. reflexivity. Qed.
Theorem exception_test_embedding s :
 bool_decide (riscv.riscv_state_exception (embedriscv_state s)=riscv.NoException) =
 bool_decide (ReducedTypes.riscv_state_exception s=ReducedTypes.NoException).
Proof. change (bool_decide (embedexception (ReducedTypes.riscv_state_exception s)=riscv.NoException)=bool_decide (ReducedTypes.riscv_state_exception s=ReducedTypes.NoException)). destruct (ReducedTypes.riscv_state_exception s); reflexivity. Qed.
Theorem next_embedding_from_run s :
 physical_mode s ->
 (let fetched := ReducedMemory.Fetch s in
  embedriscv_state (ReducedStep.Run (ReducedStep.DecodeAny (fst fetched)) (snd fetched)) =
  riscv.Run (Step.DecodeAny (embedrawInstType (fst fetched))) (embedriscv_state (snd fetched))) ->
 option_map embedriscv_state (ReducedStep.NextRISCV s) = Step.NextRISCV (embedriscv_state s).
Proof.
 intros Hp Hr; unfold ReducedStep.NextRISCV,Step.NextRISCV.
 rewrite fetch_embedding by exact Hp.
 destruct (ReducedMemory.Fetch s) as [raw fetched] eqn:Hf.
 cbn [fst snd] in *.
 rewrite <- Hr.
 rewrite exception_test_embedding,next_fetch_projection,pc_embedding,skip_embedding.
 destruct (negb (bool_decide (ReducedTypes.riscv_state_exception
 (ReducedStep.Run (ReducedStep.DecodeAny raw) fetched)=ReducedTypes.NoException))); [reflexivity|].
 destruct (ReducedStateOps.NextFetch (ReducedStep.Run (ReducedStep.DecodeAny raw) fetched)) as [control|].
 - destruct control; cbn [option_map embedTransferControl].
   + rewrite <- (write_next_fetch_embedding _ None); apply update_pc_embedding.
   + reflexivity.
 - apply update_pc_embedding.
Qed.
