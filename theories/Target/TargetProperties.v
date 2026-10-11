(** Structural target obligations inherited through the reduced projection. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.cakeml.compiler.encoders.asm Require Import asmProps.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From Galette.cakeml.compiler.encoders.riscv.proofs Require riscv_targetProof.
From InitE.Target Require Import ReducedTypes Configuration StateEmbedding StateAgreement.
Definition embedProjection (p : RiscVProjection) :=
 let '(vm,(arch,(control,(exception,(registers,(memory,pc)))))) := p in
 (vm,arch,option_map embedTransferControl control,embedexception exception,registers,memory,pc).
Theorem projection_embedding s domain :
 riscv_target.riscv_proj domain (embedriscv_state s) = embedProjection (riscvProj domain s).
Proof. reflexivity. Qed.
Theorem reduced_target_ok : target_ok riscvTarget.
Proof.
 destruct riscv_targetProof.riscv_target_ok as [Henc Hproj].
 split; [exact Henc|].
 intros s1 s2 ast Heq.
 assert (Hfull : riscv_target.riscv_proj (asmSem.mem_domain ast) (embedriscv_state s1) =
 riscv_target.riscv_proj (asmSem.mem_domain ast) (embedriscv_state s2)).
 { rewrite !projection_embedding; apply f_equal; exact Heq. }
 specialize (Hproj (embedriscv_state s1) (embedriscv_state s2) ast Hfull).
 destruct Hproj as [Hr [Hok [Hpc Hmem]]].
 split.
 - rewrite !asm_relation_embedding; exact Hr.
 - split.
   + change (riscv_target.riscv_ok (embedriscv_state s1)=riscv_target.riscv_ok (embedriscv_state s2)) in Hok.
     rewrite !validity_embedding in Hok; exact Hok.
   + split; [exact Hpc|exact Hmem].
Qed.
