(** Support facts for the original encoder's instruction paths.
    Every support claim follows from Galette's existing supported/step_pre
    hypotheses; arbitrary participant ROMs acquire no additional premise. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.examples.l3_machine_code.riscv.model Require Import riscv.
From Galette.cakeml.compiler.encoders.riscv.proofs Require riscv_targetProof.
From Galette.HOL.examples.l3_machine_code.riscv.step Require riscv_step.
From InitE.Target Require Import Decode DecodeAgreement Step StepAgreement.
Open Scope N_scope.

Theorem encoder_supported_inclusion i :
 riscv_targetProof.supported i = true -> supportedInstruction i = true.
Proof.
 intros H; riscv_targetProof.inst_cases i H;
 cbn [supportedInstruction]; reflexivity.
Qed.

Theorem encoder_word_decodes i :
 riscv_targetProof.supported i = true -> riscv.Decode (riscv.Encode i) = i.
Proof.
 intros H; riscv_targetProof.inst_cases i H.
 all: match goal with
 | |- riscv.Decode (riscv.Encode (riscv.ArithI (riscv.ADDI _))) = _ => apply riscv_targetProof.Decode_ADDI
 | |- riscv.Decode (riscv.Encode (riscv.ArithI (riscv.ORI _))) = _ => apply riscv_targetProof.Decode_ORI
 | |- riscv.Decode (riscv.Encode (riscv.ArithI (riscv.XORI _))) = _ => apply riscv_targetProof.Decode_XORI
 | |- riscv.Decode (riscv.Encode (riscv.ArithI (riscv.ANDI _))) = _ => apply riscv_targetProof.Decode_ANDI
 | |- riscv.Decode (riscv.Encode (riscv.ArithI (riscv.LUI _))) = _ => apply riscv_targetProof.Decode_LUI
 | |- riscv.Decode (riscv.Encode (riscv.ArithI (riscv.AUIPC _))) = _ => apply riscv_targetProof.Decode_AUIPC
 | |- riscv.Decode (riscv.Encode (riscv.Shift (riscv.SLLI _))) = _ => apply riscv_targetProof.Decode_SLLI
 | |- riscv.Decode (riscv.Encode (riscv.Shift (riscv.SRLI _))) = _ => apply riscv_targetProof.Decode_SRLI
 | |- riscv.Decode (riscv.Encode (riscv.Shift (riscv.SRAI _))) = _ => apply riscv_targetProof.Decode_SRAI
 | |- riscv.Decode (riscv.Encode (riscv.Shift (riscv.SLL _))) = _ => apply riscv_targetProof.Decode_SLL
 | |- riscv.Decode (riscv.Encode (riscv.Shift (riscv.SRL _))) = _ => apply riscv_targetProof.Decode_SRL
 | |- riscv.Decode (riscv.Encode (riscv.Shift (riscv.SRA _))) = _ => apply riscv_targetProof.Decode_SRA
 | |- riscv.Decode (riscv.Encode (riscv.ArithR (riscv.ADD _))) = _ => apply riscv_targetProof.Decode_ADD
 | |- riscv.Decode (riscv.Encode (riscv.ArithR (riscv.SUB _))) = _ => apply riscv_targetProof.Decode_SUB
 | |- riscv.Decode (riscv.Encode (riscv.ArithR (riscv.AND _))) = _ => apply riscv_targetProof.Decode_AND
 | |- riscv.Decode (riscv.Encode (riscv.ArithR (riscv.OR _))) = _ => apply riscv_targetProof.Decode_OR
 | |- riscv.Decode (riscv.Encode (riscv.ArithR (riscv.XOR _))) = _ => apply riscv_targetProof.Decode_XOR
 | |- riscv.Decode (riscv.Encode (riscv.ArithR (riscv.SLTU _))) = _ => apply riscv_targetProof.Decode_SLTU
 | |- riscv.Decode (riscv.Encode (riscv.MulDiv (riscv.MUL _))) = _ => apply riscv_targetProof.Decode_MUL
 | |- riscv.Decode (riscv.Encode (riscv.MulDiv (riscv.MULHU _))) = _ => apply riscv_targetProof.Decode_MULHU
 | |- riscv.Decode (riscv.Encode (riscv.MulDiv (riscv.DIV _))) = _ => apply riscv_targetProof.Decode_DIV
 | |- riscv.Decode (riscv.Encode (riscv.Load (riscv.LD _))) = _ => apply riscv_targetProof.Decode_LD
 | |- riscv.Decode (riscv.Encode (riscv.Load (riscv.LWU _))) = _ => apply riscv_targetProof.Decode_LWU
 | |- riscv.Decode (riscv.Encode (riscv.Load (riscv.LHU _))) = _ => apply riscv_targetProof.Decode_LHU
 | |- riscv.Decode (riscv.Encode (riscv.Load (riscv.LBU _))) = _ => apply riscv_targetProof.Decode_LBU
 | |- riscv.Decode (riscv.Encode (riscv.Store (riscv.SD _))) = _ => apply riscv_targetProof.Decode_SD
 | |- riscv.Decode (riscv.Encode (riscv.Store (riscv.SW _))) = _ => apply riscv_targetProof.Decode_SW
 | |- riscv.Decode (riscv.Encode (riscv.Store (riscv.SH _))) = _ => apply riscv_targetProof.Decode_SH
 | |- riscv.Decode (riscv.Encode (riscv.Store (riscv.SB _))) = _ => apply riscv_targetProof.Decode_SB
 | |- riscv.Decode (riscv.Encode (riscv.Branch (riscv.JAL _))) = _ => apply riscv_targetProof.Decode_JAL
 | |- riscv.Decode (riscv.Encode (riscv.Branch (riscv.JALR _))) = _ => apply riscv_targetProof.Decode_JALR
 | |- riscv.Decode (riscv.Encode (riscv.Branch (riscv.BEQ _))) = _ => apply riscv_targetProof.Decode_BEQ
 | |- riscv.Decode (riscv.Encode (riscv.Branch (riscv.BNE _))) = _ => apply riscv_targetProof.Decode_BNE
 | |- riscv.Decode (riscv.Encode (riscv.Branch (riscv.BLT _))) = _ => apply riscv_targetProof.Decode_BLT
 | |- riscv.Decode (riscv.Encode (riscv.Branch (riscv.BLTU _))) = _ => apply riscv_targetProof.Decode_BLTU
 | |- riscv.Decode (riscv.Encode (riscv.Branch (riscv.BGE _))) = _ => apply riscv_targetProof.Decode_BGE
 | |- riscv.Decode (riscv.Encode (riscv.Branch (riscv.BGEU _))) = _ => apply riscv_targetProof.Decode_BGEU
 end.
Qed.

Theorem reduced_encoder_word_decodes i :
 riscv_targetProof.supported i = true -> Decode.Decode (riscv.Encode i) = i.
Proof.
 intros H; rewrite decoder_agreement,encoder_word_decodes by exact H.
 unfold restrictInstruction; rewrite encoder_supported_inclusion by exact H; reflexivity.
Qed.

Theorem encoder_word_uncompressed i :
 riscv_targetProof.supported i = true ->
 word_bit 1 (riscv.Encode i) = true /\ word_bit 0 (riscv.Encode i) = true.
Proof.
 intros H; split; riscv_targetProof.inst_cases i H;
 cbn [riscv.Encode riscv.Rtype riscv.Itype riscv.Stype riscv.SBtype riscv.Utype riscv.UJtype];
 unfold riscv.opc; riscv_targetProof.wbs; reflexivity.
Qed.

Theorem encoded_fetch s i :
 riscv_targetProof.supported i = true ->
 riscv_targetProof.s_VM s = n2w 0 ->
 riscv_targetProof.bytes_at s (riscv.Encode i) ->
 riscv_step.Fetch s = (riscv.Word (riscv.Encode i),riscv.write'Skip (n2w 4) s).
Proof.
 intros H HV Hb; destruct (encoder_word_uncompressed i H) as [H1 H0].
 apply riscv_targetProof.Fetch_word; assumption.
Qed.

Theorem encoded_fetch_support s i :
 riscv_targetProof.supported i = true ->
 riscv_targetProof.s_VM s = n2w 0 ->
 riscv_targetProof.bytes_at s (riscv.Encode i) ->
 exists fetched,
 riscv_step.Fetch s = (riscv.Word (riscv.Encode i),fetched) /\
 supportedInstruction (riscv.Decode (riscv.Encode i)) = true.
Proof.
 intros H HV Hb; exists (riscv.write'Skip (n2w 4) s); split.
 - apply encoded_fetch; assumption.
 - rewrite encoder_word_decodes by exact H; apply encoder_supported_inclusion; exact H.
Qed.

Theorem encoded_word_step_agreement s i :
 riscv_targetProof.supported i = true ->
 riscv_targetProof.s_VM s = n2w 0 ->
 riscv_targetProof.bytes_at s (riscv.Encode i) ->
 Step.NextRISCV s = riscv_step.NextRISCV s.
Proof.
 intros H HV Hb; destruct (encoded_fetch_support s i H HV Hb) as [fetched [HF HS]].
 apply (step_agreement_on_supported_word s (riscv.Encode i) fetched); assumption.
Qed.

Theorem step_pre_fetch_support dom s A i :
 riscv_targetProof.rv_rel dom s A -> riscv_targetProof.step_pre dom A i ->
 exists fetched,
 riscv_step.Fetch s = (riscv.Word (riscv.Encode i),fetched) /\
 supportedInstruction (riscv.Decode (riscv.Encode i)) = true.
Proof.
 intros Hr Hp.
 pose proof Hr as [Hok _]; apply riscv_targetProof.riscv_ok_iff in Hok.
 destruct Hok as [[HV _] _].
 pose proof Hp as [Hsup [Hb _]].
 apply encoded_fetch_support; try assumption.
 apply (riscv_targetProof.bytes_at_intro dom s A i); assumption.
Qed.

Theorem step_pre_word_step_agreement dom s A i :
 riscv_targetProof.rv_rel dom s A -> riscv_targetProof.step_pre dom A i ->
 Step.NextRISCV s = riscv_step.NextRISCV s.
Proof.
 intros Hr Hp; destruct (step_pre_fetch_support dom s A i Hr Hp) as [fetched [HF HS]].
 apply (step_agreement_on_supported_word s (riscv.Encode i) fetched); assumption.
Qed.

Theorem run_ok2_supported dom A instructions :
 riscv_targetProof.run_ok2 dom A instructions ->
 Forall (fun i => supportedInstruction i = true) instructions.
Proof.
 revert A; induction instructions as [|i rest IH]; intros A H.
 - constructor.
 - cbn [riscv_targetProof.run_ok2] in H; destruct H as [[Hsup _] Hrest].
   constructor.
   + apply encoder_supported_inclusion; exact Hsup.
   + apply (IH (riscv_targetProof.aexec i A)); exact Hrest.
Qed.

Theorem run_ok_supported dom A instructions PA :
 riscv_targetProof.run_ok dom A instructions PA ->
 Forall (fun i => supportedInstruction i = true) instructions.
Proof.
 intros H; apply (run_ok2_supported dom A instructions).
 apply (riscv_targetProof.run_ok_ok2 dom instructions A PA); exact H.
Qed.
