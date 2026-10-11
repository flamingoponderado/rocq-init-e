(** One encoded instruction preserves Galettes abstract execution relation. *)
From Galette Require Import Base.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From Galette.HOL.examples.l3_machine_code.riscv.step Require riscv_step.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From Galette.cakeml.compiler.encoders.riscv.proofs Require Import riscv_targetProof.
From InitE.Target Require Import Configuration StateEmbedding StateAgreement
 CompilerStepBridge EncoderSupport.
Theorem reduced_one_step dom s A i :
 rv_rel dom (embedriscv_state s) A -> step_pre dom A i ->
 rv_rel dom (embedriscv_state (Configuration.riscvNext s)) (aexec i A) /\
 (forall x, ~dom x -> ReducedTypes.riscv_state_MEM8 (Configuration.riscvNext s) x = ReducedTypes.riscv_state_MEM8 s x).
Proof.
 intros Hr Hp.
 pose proof Hr as (Hok & Hg & Hpc & Hm).
 pose proof Hp as (Hsup & Hb & Hmo & Hacc & Hal).
 pose proof Hok as Hok'; apply riscv_ok_iff in Hok' as (Hs & Hpal).
 assert (Hg' : aregs A = aregs (obs (embedriscv_state s))) by exact (eq_sym Hg).
 destruct (step_thm (embedriscv_state s) i Hsup Hs Hpal
 (bytes_at_intro dom (embedriscv_state s) A i Hr Hb)
 (mem_ok_regs i A (obs (embedriscv_state s)) Hg' Hmo)) as (next & HN & Hs' & Ho).
 destruct (step_pre_fetch_support dom (embedriscv_state s) A i Hr Hp) as [fetched [HF HS]].
 rewrite validity_embedding in Hok.
 pose proof (successful_target_next s (riscv.Encode i) fetched next Hok HF HS HN) as HE.
 pose proof (one_step dom (embedriscv_state s) A i Hr Hp) as [HR HM].
 rewrite <- HE in HR,HM.
 split; [exact HR|exact HM].
Qed.
