(** Checked execution of each original five-operation copy-loop body. *)
From Galette Require Import Base.
From Stdlib Require Import NArith Lia.
From Galette.HOL.src.n_bit Require Import words alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.relation Require Import relation.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From InitE.InitE Require Import Parameters BaselineArtifactLayout.
From InitE.Baseline Require Import BootstrapProgram BootstrapMemory BootstrapSteps BootstrapPrefix BootstrapCopy BootstrapCopyLoop BootstrapCopyBounds BootstrapCopyInvariant BootstrapTail BootstrapCodeFacts.
Open Scope N_scope.
Definition CopyCodeAgreement (s : asm_state 64) : Prop :=
 forall x, initialPc <= w2n x -> w2n x < initialPc+208 -> mem s x = romMemory x.
Lemma copy_control_code k s : k <= 4606 -> CopyBytes k s -> CopyCodeAgreement s.
Proof.
 intros Hk [_ Hframe] x Hlo Hhi; apply Hframe; copy_numbers; lia.
Qed.
Lemma copy_load_memory s : be s = false -> mem (after s copyLoad) = mem s.
Proof.
 intro Hb; rewrite after_copyLoad,upd_pc_memory.
 exact (proj1 (load_frame s Hb)).
Qed.
Lemma copy_load_pc s : pc (after s copyLoad) = (pc s+n2w 4)%w.
Proof. reflexivity. Qed.
Lemma copy_store_pc s : pc (after s copyStore) = (pc s+n2w 4)%w.
Proof. reflexivity. Qed.
Lemma copy_add_memory s r : mem (after s (bootAdd r)) = mem s.
Proof. rewrite after_bootAdd,upd_pc_memory,upd_reg_memory; reflexivity. Qed.
Lemma copy_add_failure s r : failed (after s (bootAdd r)) = failed s.
Proof. rewrite after_bootAdd,upd_pc_failure,upd_reg_failure; reflexivity. Qed.
Lemma copy_add_pc s r : pc (after s (bootAdd r)) = (pc s+n2w 4)%w.
Proof. reflexivity. Qed.
Lemma copy_load_failure k s : k < 4606 -> CopyControl k s ->
 failed (after s copyLoad) = false.
Proof.
 intros Hk [H5 H6 H7 Hb Hd Hl Ha Hf Hp].
 rewrite after_copyLoad,upd_pc_failure,load_success_failure.
 - exact Hf.
 - exact Hb.
 - intros j Hj; rewrite Hd,H5; apply copy_source_domain; assumption.
 - rewrite H5; apply copy_address_alignment; auto.
Qed.
Lemma copy_pair_failure k s : k < 4606 -> CopyControl k s ->
 failed (after (after s copyLoad) copyStore) = false.
Proof.
 intros Hk [H5 H6 H7 Hb Hd Hl Ha Hf Hp].
 rewrite copy_pair_after,upd_pc_failure; apply copyWord_success.
 - exact Hb.
 - exact Hf.
 - intros j Hj; rewrite Hd,H5; apply copy_source_domain; assumption.
 - intros j Hj; rewrite Hd,H6; apply copy_destination_domain; assumption.
 - rewrite H5; apply copy_address_alignment; auto.
 - rewrite H6; apply copy_address_alignment; auto.
Qed.
Lemma copy_load_code s : be s = false -> CopyCodeAgreement s -> CopyCodeAgreement (after s copyLoad).
Proof. intros Hb Hcode x Hlo Hhi; rewrite copy_load_memory by exact Hb; apply Hcode; assumption. Qed.
Lemma copy_pair_code k s : k < 4606 -> CopyControl k s -> CopyCodeAgreement s ->
 CopyCodeAgreement (after (after s copyLoad) copyStore).
Proof.
 intros Hk [H5 H6 H7 Hb Hd Hl Ha Hf Hp] Hcode x Hlo Hhi.
 rewrite copy_pair_after,upd_pc_memory,copyWord_frame.
 - apply Hcode; assumption.
 - exact Hb.
 - intros j Hj E; apply (f_equal w2n) in E; rewrite H6,copy_address_value in E by (auto; lia).
   copy_numbers; lia.
Qed.
Lemma copy_add_code s r : CopyCodeAgreement s -> CopyCodeAgreement (after s (bootAdd r)).
Proof. intros Hcode x Hlo Hhi; rewrite copy_add_memory; apply Hcode; assumption. Qed.
Lemma copy_iteration_run s : copyIteration s = runCode copyLoopCode s.
Proof. reflexivity. Qed.
Lemma copy_iteration_last s : copyIteration s =
 after (after (after (after (after s copyLoad) copyStore) (bootAdd 5)) (bootAdd 6))
 (JumpCmp Lower 6 (Reg 7) (word_2comp (n2w 16))).
Proof. reflexivity. Qed.
Local Opaque after copyWord copyIteration.

Ltac copy_check_controls := repeat first [rewrite tail_after_be|rewrite tail_after_lr|
 rewrite tail_after_align|rewrite tail_after_mem_domain].
Ltac copy_check_pc := repeat first [rewrite copy_add_pc|rewrite copy_load_pc|rewrite copy_store_pc].
Ltac copy_check_bytes address Hp Hd Hcode :=
 apply (tail_checked_bytes _ address);
 [ vm_compute; tauto |
   copy_check_pc; rewrite Hp; vm_compute; reflexivity |
   copy_check_controls; exact Hd |
   exact Hcode ].
Theorem copy_body_checked k s : k < 4606 -> CopyControl k s -> CopyCodeAgreement s ->
 Checked copyLoopCode s.
Proof.
 intros Hk Hcontrol Hcode.
 pose proof Hcontrol as Hfull.
 pose proof (copy_load_failure k s Hk Hcontrol) as F1.
 pose proof (copy_pair_failure k s Hk Hcontrol) as F2.
 destruct Hcontrol as [H5 H6 H7 Hb Hd Hl Ha Hf Hp].
 assert (Ek : (k <? 4606) = true) by (apply N.ltb_lt; exact Hk); rewrite Ek in Hp.
 pose proof (copy_load_code s Hb Hcode) as M1.
 assert (M2 : CopyCodeAgreement (after (after s copyLoad) copyStore)).
 { apply copy_pair_code with (k:=k); [exact Hk|exact Hfull|exact Hcode]. }
 pose proof (copy_add_code _ 5 M2) as M3.
 pose proof (copy_add_code _ 6 M3) as M4.
 cbn [Checked copyLoopCode]; split.
 - apply checked_step.
   + copy_check_bytes 0x80000018 Hp Hd Hcode.
   + exact Hl.
   + exact Hb.
   + exact Ha.
   + rewrite F1; discriminate.
   + vm_compute; reflexivity.
 - split.
   + apply checked_step.
     * copy_check_bytes 0x8000001c Hp Hd M1.
     * copy_check_controls; exact Hl.
     * copy_check_controls; exact Hb.
     * copy_check_controls; exact Ha.
     * rewrite F2; discriminate.
     * vm_compute; reflexivity.
   + split.
     * apply checked_step.
       -- copy_check_bytes 0x80000020 Hp Hd M2.
       -- copy_check_controls; exact Hl.
       -- copy_check_controls; exact Hb.
       -- copy_check_controls; exact Ha.
       -- rewrite copy_add_failure,F2; discriminate.
       -- vm_compute; reflexivity.
     * split.
       -- apply checked_step.
          ++ copy_check_bytes 0x80000024 Hp Hd M3.
          ++ copy_check_controls; exact Hl.
          ++ copy_check_controls; exact Hb.
          ++ copy_check_controls; exact Ha.
          ++ rewrite !copy_add_failure,F2; discriminate.
          ++ vm_compute; reflexivity.
       -- split; [|exact I]. apply checked_step.
          ++ copy_check_bytes 0x80000028 Hp Hd M4.
          ++ copy_check_controls; exact Hl.
          ++ copy_check_controls; exact Hb.
          ++ copy_check_controls; exact Ha.
          ++ rewrite <- copy_iteration_last.
             rewrite copy_iteration_success with (s:=s); [discriminate|exact Hb|exact Hf| | | | ].
             ** intros j Hj; rewrite Hd,H5; apply copy_source_domain; assumption.
             ** intros j Hj; rewrite Hd,H6; apply copy_destination_domain; assumption.
             ** rewrite H5; apply copy_address_alignment; auto.
             ** rewrite H6; apply copy_address_alignment; auto.
          ++ vm_compute; reflexivity.
Qed.

Theorem copy_body_state_checked k : k < 4606 -> Checked copyLoopCode (copyState k).
Proof.
 intro Hk; apply copy_body_checked with (k:=k).
 - exact Hk.
 - apply copy_control_all; lia.
 - apply copy_control_code with (k:=k); [lia|apply copy_bytes_all; lia].
Qed.
Theorem copy_body_state_trace k : k < 4606 ->
 RTC (fun before post => exists i, asm_step riscv_target.riscv_config before i post)
 (copyState k) (copyState (N.succ k)).
Proof.
 intro Hk; rewrite copy_state_successor,copy_iteration_run.
 apply checked_trace; apply copy_body_state_checked; exact Hk.
Qed.
Theorem copy_loop_checked_trace k : k <= 4606 ->
 RTC (fun before post => exists i, asm_step riscv_target.riscv_config before i post)
 copyEntryAsm (copyState k).
Proof.
 induction k using N.peano_ind; intro Hk.
 - rewrite copy_state_zero; apply rtc_refl.
 - eapply RTC_RTC with (y:=copyState k).
   + apply IHk; lia.
   + apply copy_body_state_trace; lia.
Qed.
Definition bootstrapEndpoint : asm_state 64 := runCode tailCode (copyState 4606).
Theorem full_bootstrap_checked_trace :
 RTC (fun before post => exists i, asm_step riscv_target.riscv_config before i post)
 initialAsm bootstrapEndpoint.
Proof.
 eapply RTC_RTC with (y:=copyEntryAsm).
 - exact prefix_checked_trace.
 - eapply RTC_RTC with (y:=copyState 4606).
   + apply copy_loop_checked_trace; lia.
   + unfold bootstrapEndpoint; apply checked_trace; apply tail_checked.
     * exact (copy_pc 4606 (copyState 4606) (copy_control_all 4606 ltac:(lia))).
     * exact (copy_endian 4606 (copyState 4606) (copy_control_all 4606 ltac:(lia))).
     * exact (copy_domain 4606 (copyState 4606) (copy_control_all 4606 ltac:(lia))).
     * exact (copy_link 4606 (copyState 4606) (copy_control_all 4606 ltac:(lia))).
     * exact (copy_alignment 4606 (copyState 4606) (copy_control_all 4606 ltac:(lia))).
     * exact (copy_failed 4606 (copyState 4606) (copy_control_all 4606 ltac:(lia))).
     * apply copy_control_code with (k:=4606); [lia|apply copy_bytes_all; lia].
Qed.
