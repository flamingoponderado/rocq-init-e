(** Successful encoded-step transfer. These are proof-side hypotheses;
    the arbitrary-submission challenge retains its original statement. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From Galette.HOL.examples.l3_machine_code.riscv.step Require riscv_step.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From InitE.Target Require Import ReducedTypes ReducedStep Configuration
 StateEmbedding NextAgreement DecodeAgreement StepAgreement.
Theorem supported_next_embedding s w fetched :
 Configuration.riscvOk s = true ->
 riscv_step.Fetch (embedriscv_state s) = (riscv.Word w,fetched) ->
 supportedInstruction (riscv.Decode w) = true ->
 option_map embedriscv_state (ReducedStep.NextRISCV s) = riscv_step.NextRISCV (embedriscv_state s).
Proof.
 intros H HF HS; rewrite reduced_next_embedding by exact H.
 apply step_agreement_on_supported_word with w fetched; assumption.
Qed.
Theorem successful_supported_step s w fetched full_next :
 Configuration.riscvOk s = true ->
 riscv_step.Fetch (embedriscv_state s) = (riscv.Word w,fetched) ->
 supportedInstruction (riscv.Decode w) = true ->
 riscv_step.NextRISCV (embedriscv_state s) = Some full_next ->
 exists reduced_next, ReducedStep.NextRISCV s = Some reduced_next /\
 embedriscv_state reduced_next = full_next.
Proof.
 intros H HF HS HN.
 pose proof (supported_next_embedding s w fetched H HF HS) as HE.
 rewrite HN in HE.
 destruct (ReducedStep.NextRISCV s) as [next|] eqn:HR; [|discriminate].
 cbn in HE; injection HE as E; exists next; split; [reflexivity|exact E].
Qed.

Theorem successful_target_next s w fetched full_next :
 Configuration.riscvOk s = true ->
 riscv_step.Fetch (embedriscv_state s) = (riscv.Word w,fetched) ->
 supportedInstruction (riscv.Decode w) = true ->
 riscv_step.NextRISCV (embedriscv_state s) = Some full_next ->
 embedriscv_state (Configuration.riscvNext s) =
 riscv_target.riscv_next (embedriscv_state s).
Proof.
 intros H HF HS HN.
 destruct (successful_supported_step s w fetched full_next H HF HS HN) as [next [HR HE]].
 unfold Configuration.riscvNext,riscv_target.riscv_next; rewrite HR,HN.
 exact HE.
Qed.
