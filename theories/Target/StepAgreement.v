(** A baseline bridge; these hypotheses describe an encoded instruction
    step and do not alter the arbitrary-submission challenge premises. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.examples.l3_machine_code.riscv.model Require Import riscv.
From Galette.HOL.examples.l3_machine_code.riscv.step Require riscv_step.
From InitE.Target Require Import DecodeAgreement Step.
Theorem step_agreement_on_supported_word s w fetched :
 riscv_step.Fetch s = (Word w,fetched) ->
 supportedInstruction (riscv.Decode w) = true ->
 Step.NextRISCV s = riscv_step.NextRISCV s.
Proof.
 intros HF HS; unfold Step.NextRISCV, riscv_step.NextRISCV; rewrite HF.
 cbn [Step.DecodeAny riscv_step.DecodeAny].
 rewrite decoder_agreement; unfold restrictInstruction; rewrite HS; reflexivity.
Qed.
