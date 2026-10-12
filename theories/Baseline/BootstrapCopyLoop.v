(** Original five-instruction bitmap-copy loop; actual ASM execution. *)
From Galette Require Import Base.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From InitE.Baseline Require Import BootstrapProgram BootstrapSteps BootstrapPrefix BootstrapCopy BootstrapMemoryControl.
Open Scope N_scope.
Definition copyLoad : asm.asm 64 := Inst (Mem Load 28 (Addr 5 (n2w 0))).
Definition copyStore : asm.asm 64 := Inst (Mem Store 28 (Addr 6 (n2w 0))).
Definition copyLoopCode : list (asm.asm 64) :=
 [copyLoad;copyStore;bootAdd 5;bootAdd 6;JumpCmp Lower 6 (Reg 7) (word_2comp (n2w 16))].
Definition copyIteration (s : asm_state 64) := runCode copyLoopCode s.
Theorem copy_loop_original : copyLoopCode = MAP snd (TAKE 5 (DROP 3 bootstrapBlocks)).
Proof. reflexivity. Qed.
Theorem copy_loop_admitted :
 EVERY (fun i => asm_ok i riscv_target.riscv_config) copyLoopCode = true.
Proof. vm_compute; reflexivity. Qed.
Lemma upd_pc_current {a} p (s : asm_state a) : pc (upd_pc p s) = p.
Proof. reflexivity. Qed.
Lemma upd_pc_twice {a} p q (s : asm_state a) : upd_pc p (upd_pc q s) = upd_pc p s.
Proof. reflexivity. Qed.
Lemma after_copyLoad s : after s copyLoad =
 upd_pc (pc s+n2w 4)%w (mem_load 8 28 (Addr 5 (n2w 0)) s).
Proof. reflexivity. Qed.
Lemma after_copyStore s : after s copyStore =
 upd_pc (pc s+n2w 4)%w (mem_store 8 28 (Addr 6 (n2w 0)) s).
Proof. reflexivity. Qed.
Theorem copy_pair_after s : after (after s copyLoad) copyStore =
 upd_pc (pc s+n2w 8)%w (copyWord s).
Proof.
 rewrite after_copyStore,after_copyLoad,upd_pc_current,mem_store_upd_pc,upd_pc_twice.
 fold copyWord; rewrite <- WORD_ADD_ASSOC,word_add_n2w; reflexivity.
Qed.

Lemma after_bootAdd s r : after s (bootAdd r) =
 upd_pc (pc s+n2w 4)%w (upd_reg r (regs s r+n2w 8)%w s).
Proof. reflexivity. Qed.
Lemma after_copyBranch s :
 after s (JumpCmp Lower 6 (Reg 7) (word_2comp (n2w 16))) =
 if word_cmp Lower (regs s 6) (regs s 7)
 then upd_pc (pc s+word_2comp (n2w 16))%w s
 else upd_pc (pc s+n2w 4)%w s.
Proof. reflexivity. Qed.

Lemma upd_pc_registers {a} p (s : asm_state a) : regs (upd_pc p s) = regs s.
Proof. reflexivity. Qed.
Lemma upd_reg_program_counter {a} r value (s : asm_state a) : pc (upd_reg r value s) = pc s.
Proof. reflexivity. Qed.
Lemma upd_reg_registers {a} r value (s : asm_state a) :
 regs (upd_reg r value s) = UPDATE r value (regs s).
Proof. reflexivity. Qed.
Theorem copy_iteration_equation s : be s = false ->
 copyIteration s =
 let changed := upd_reg 6 (regs s 6+n2w 8)%w
  (upd_reg 5 (regs s 5+n2w 8)%w (copyWord s)) in
 if word_cmp Lower (regs s 6+n2w 8)%w (regs s 7)
 then upd_pc (pc s+n2w 16+word_2comp (n2w 16))%w changed
 else upd_pc (pc s+n2w 20)%w changed.
Proof.
 intro Hb; cbn [copyIteration copyLoopCode runCode].
 rewrite copy_pair_after,!after_bootAdd,after_copyBranch.
 rewrite !upd_pc_current,!upd_pc_registers,!upd_reg_registers.
 rewrite !updateN_eqb; cbn [N.eqb].
 rewrite !copyWord_other_register by (assumption || discriminate).
 rewrite !upd_reg_upd_pc,!upd_pc_twice.
 rewrite <- !WORD_ADD_ASSOC,!word_add_n2w.
 reflexivity.
Qed.

Theorem copy_iteration_normal_form s : be s = false ->
 copyIteration s =
 let changed := upd_reg 6 (regs s 6+n2w 8)%w
  (upd_reg 5 (regs s 5+n2w 8)%w (copyWord s)) in
 upd_pc (if word_cmp Lower (regs s 6+n2w 8)%w (regs s 7)
  then pc s else (pc s+n2w 20)%w) changed.
Proof.
 intro Hb; rewrite copy_iteration_equation by exact Hb.
 rewrite <- WORD_ADD_ASSOC,WORD_ADD_RINV,(proj1 WORD_ADD_0).
 destruct (word_cmp Lower (regs s 6+n2w 8)%w (regs s 7)); reflexivity.
Qed.

Lemma upd_pc_memory {a} p (s : asm_state a) : mem (upd_pc p s) = mem s.
Proof. reflexivity. Qed.
Lemma upd_reg_memory {a} r value (s : asm_state a) : mem (upd_reg r value s) = mem s.
Proof. reflexivity. Qed.
Lemma upd_reg_endian {a} r value (s : asm_state a) : be (upd_reg r value s) = be s.
Proof. reflexivity. Qed.
Lemma upd_reg_domain {a} r value (s : asm_state a) : mem_domain (upd_reg r value s) = mem_domain s.
Proof. reflexivity. Qed.
Lemma upd_reg_link {a} r value (s : asm_state a) : lr (upd_reg r value s) = lr s.
Proof. reflexivity. Qed.
Lemma upd_reg_alignment {a} r value (s : asm_state a) : align (upd_reg r value s) = align s.
Proof. reflexivity. Qed.
Lemma upd_pc_link {a} p (s : asm_state a) : lr (upd_pc p s) = lr s.
Proof. reflexivity. Qed.
Lemma upd_pc_alignment {a} p (s : asm_state a) : align (upd_pc p s) = align s.
Proof. reflexivity. Qed.
Lemma upd_pc_failure {a} p (s : asm_state a) : failed (upd_pc p s) = failed s.
Proof. reflexivity. Qed.
Local Opaque copyWord copyIteration.


Theorem copy_iteration_registers s : be s = false ->
 regs (copyIteration s) =
 UPDATE 6 (regs s 6+n2w 8)%w
  (UPDATE 5 (regs s 5+n2w 8)%w (regs (copyWord s))).
Proof.
 intro Hb; rewrite copy_iteration_normal_form by exact Hb; reflexivity.
Qed.
Theorem copy_iteration_counters s : be s = false ->
 regs (copyIteration s) 5 = (regs s 5+n2w 8)%w /\
 regs (copyIteration s) 6 = (regs s 6+n2w 8)%w /\
 regs (copyIteration s) 7 = regs s 7.
Proof.
 intro Hb; rewrite copy_iteration_registers by exact Hb.
 rewrite !updateN_eqb; cbn [N.eqb].
 rewrite copyWord_other_register by (assumption || discriminate).
 repeat split; reflexivity.
Qed.
Theorem copy_iteration_memory s : be s = false ->
 mem (copyIteration s) = mem (copyWord s).
Proof.
 intro Hb.
 rewrite (copy_iteration_normal_form s Hb) at 1.
 rewrite upd_pc_memory, !upd_reg_memory.
 reflexivity.
Qed.
Theorem copy_iteration_controls s : be s = false ->
 be (copyIteration s) = be s /\
 mem_domain (copyIteration s) = mem_domain s /\
 lr (copyIteration s) = lr s /\
 align (copyIteration s) = align s.
Proof.
 intro Hb; rewrite copy_iteration_normal_form by exact Hb.
 rewrite upd_pc_endian, upd_pc_domain, upd_pc_link, upd_pc_alignment.
 rewrite !upd_reg_endian, !upd_reg_domain, !upd_reg_link, !upd_reg_alignment.
 repeat apply conj; [apply copyWord_endian|apply copyWord_domain|apply copyWord_link|apply copyWord_alignment].
Qed.
Theorem copy_iteration_success s : be s = false -> failed s = false ->
 (forall j, j < 8 -> mem_domain s (regs s 5+n2w j)%w) ->
 (forall j, j < 8 -> mem_domain s (regs s 6+n2w j)%w) ->
 aligned 3 (regs s 5) = true -> aligned 3 (regs s 6) = true ->
 failed (copyIteration s) = false.
Proof.
 intros Hb Hf Hsrc Hdst Ha Hbnd; rewrite copy_iteration_normal_form by exact Hb.
 rewrite upd_pc_failure, !upd_reg_failure; apply copyWord_success; assumption.
Qed.

Theorem copy_iteration_selected s j : be s = false -> j < 8 ->
 mem (copyIteration s) (regs s 6+n2w j)%w = mem s (regs s 5+n2w j)%w.
Proof.
 intros Hb Hj; rewrite copy_iteration_memory by exact Hb.
 apply copyWord_selected; assumption.
Qed.
Theorem copy_iteration_frame s x : be s = false ->
 (forall j, j < 8 -> x <> (regs s 6+n2w j)%w) ->
 mem (copyIteration s) x = mem s x.
Proof.
 intros Hb Hout; rewrite copy_iteration_memory by exact Hb.
 apply copyWord_frame; assumption.
Qed.
Theorem copy_iteration_other_register s r : be s = false ->
 r <> 5 -> r <> 6 -> r <> 28 -> regs (copyIteration s) r = regs s r.
Proof.
 intros Hb H5 H6 H28; rewrite copy_iteration_registers by exact Hb.
 unfold UPDATE; destruct (decide (6=r)); [congruence|].
 destruct (decide (5=r)); [congruence|].
 apply copyWord_other_register; assumption.
Qed.
