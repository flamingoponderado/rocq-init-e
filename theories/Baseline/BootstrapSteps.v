(** Original BootstrapSteps.lean: proved assembly traces lift to the actual
    reduced target and evaluator; no post-bootstrap state is assumed. *)
From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.relation Require Import relation.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem targetProps.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.misc Require Import misc.
From InitE.Target Require Import ReducedTypes Configuration ReducedEncoderCases.
Open Scope N_scope.
Definition after (s : asm_state 64) (i : asm.asm 64) : asm_state 64 :=
 asmSem.asm i (pc s + n2w (LENGTH (riscv_target.riscv_enc i)))%w s.
Theorem checked_step (s : asm_state 64) (i : asm.asm 64) :
 bytes_in_memory (pc s) (riscv_target.riscv_enc i) (mem s) (mem_domain s) ->
 lr s = 1 -> be s = false -> align s = 2 ->
 ~ failed (after s i) -> asm_ok i riscv_target.riscv_config = true ->
 asm_step riscv_target.riscv_config s i (after s i).
Proof. intros Hb Hl He Ha Hf Hi; repeat split; assumption || reflexivity. Qed.
Theorem trace_simulation (s final : asm_state 64) (ms : riscv_state) :
 target_state_rel riscvTarget s ms ->
 RTC (fun before after => exists i,
   asm_step riscv_target.riscv_config before i after) s final ->
 exists n, target_state_rel riscvTarget final (FUNPOW riscvNext n ms).
Proof.
 intros Hr Ht.
 apply (encoder_correct_RTC_asm_step_target_state_rel riscvTarget s ms final).
 split; [exact reduced_riscv_encoder_correct|]. split; assumption.
Qed.
Theorem step_evaluator {F : Type}
 (mc : machine_config 64 riscv_state RiscVProjection)
 (s : asm_state 64) ms (io : ffi_state F) (i : asm.asm 64) :
 target mc = riscvTarget -> prog_addresses mc = mem_domain s ->
 ffi_entry_pcs_disjoint mc s (LENGTH (riscv_target.riscv_enc i)) ->
 interference_ok (next_interfer mc) (proj riscvTarget (mem_domain s)) ->
 asm_step riscv_target.riscv_config s i (after s i) ->
 target_state_rel riscvTarget s ms ->
 exists l ms2,
 (forall k, evaluate mc io (k+l) ms = evaluate (shift_interfer l mc) io k ms2) /\
 target_state_rel riscvTarget (after s i) ms2 /\ l <> 0.
Proof.
 intros Htarget Hdomain Hdisjoint Hinter Hstep Hrel.
 pose proof (asm_step_IMP_evaluate_step mc s ms io i) as H.
 rewrite Htarget in H.
 apply H.
 exact (conj reduced_riscv_encoder_correct
  (conj Hdomain (conj Hdisjoint (conj Hinter (conj Hstep Hrel))))).
Qed.

Theorem after_const s r (value : word 64) :
 after s (Inst (Const r value)) =
 upd_pc (pc s+n2w (LENGTH (riscv_target.riscv_enc (Inst (Const r value)))))%w
 (upd_reg r value s).
Proof. reflexivity. Qed.
Theorem after_add s dest source (value : word 64) :
 after s (Inst (Arith (Binop Add dest source (Imm value)))) =
 upd_pc (pc s+n2w (LENGTH (riscv_target.riscv_enc
 (Inst (Arith (Binop Add dest source (Imm value)))))))%w
 (upd_reg dest (regs s source+value)%w s).
Proof. reflexivity. Qed.
Theorem after_jump s (offset : word 64) :
 after s (Jump offset) = upd_pc (pc s+offset)%w s.
Proof. reflexivity. Qed.
Theorem after_loc s r (offset : word 64) :
 after s (Loc r offset) =
 upd_pc (pc s+n2w (LENGTH (riscv_target.riscv_enc (Loc r offset))))%w
 (upd_reg r (pc s+offset)%w s).
Proof. reflexivity. Qed.
