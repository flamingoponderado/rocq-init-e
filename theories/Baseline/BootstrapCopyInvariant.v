(** Control invariant of the actual full original bitmap-copy loop. *)
From Galette Require Import Base.
From Stdlib Require Import NArith Lia Bool.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem.
From InitE.InitE Require Import BaselineArtifactLayout.
From InitE.Baseline Require Import BootstrapMemory BootstrapProgram BootstrapCopyLoop BootstrapCopyBounds.
Open Scope N_scope.
Definition copyState k : asm_state 64 := FUNPOW copyIteration k copyEntryAsm.
Lemma copy_state_zero : copyState 0 = copyEntryAsm.
Proof. apply FUNPOW_0. Qed.
Lemma copy_state_successor k : copyState (N.succ k) = copyIteration (copyState k).
Proof. unfold copyState; apply FUNPOW_SUC. Qed.
Local Opaque copyState copyIteration.
Record CopyControl (k : N) (s : asm_state 64) : Prop := {
 copy_source : regs s 5 = n2w (initDataRom+8*k);
 copy_destination : regs s 6 = n2w (initDataRam+8*k);
 copy_end : regs s 7 = n2w initDataEnd;
 copy_endian : be s = false;
 copy_domain : mem_domain s = bootstrapDomain;
 copy_link : lr s = 1;
 copy_alignment : align s = 2;
 copy_failed : failed s = false;
 copy_pc : pc s = if k <? 4606 then n2w 0x80000018 else n2w 0x8000002c
}.
Lemma copy_counter_advance base k :
 (n2w (base+8*k)+n2w 8 : word 64)%w = n2w (base+8*N.succ k).
Proof. rewrite word_add_n2w; f_equal; lia. Qed.
Lemma copy_branch_bound k : k < 4606 ->
 word_cmp Lower (n2w (initDataRam+8*N.succ k) : word 64) (n2w initDataEnd) =
 (N.succ k <? 4606).
Proof.
 intro Hk; apply Bool.eq_true_iff_eq.
 change (is_true ((n2w (initDataRam+8*N.succ k) : word 64) <+ n2w initDataEnd)%w <-> (N.succ k <? 4606) = true).
 rewrite WORD_LO, N.ltb_lt, !w2n_n2w.
 change (dimword 64) with (2^64).
 rewrite !N.mod_small by (copy_numbers; lia).
 copy_numbers; lia.
Qed.
Theorem copy_control_initial : CopyControl 0 copyEntryAsm.
Proof. constructor; reflexivity. Qed.
Theorem copy_control_step k s : k < 4606 -> CopyControl k s ->
 CopyControl (N.succ k) (copyIteration s).
Proof.
 intros Hk H; destruct H as [H5 H6 H7 Hb Hd Hl Ha Hf Hp].
 destruct (copy_iteration_counters s Hb) as [C5 [C6 C7]].
 destruct (copy_iteration_controls s Hb) as [Cb [Cd [Cl Ca]]].
 constructor.
 - rewrite C5,H5; apply copy_counter_advance.
 - rewrite C6,H6; apply copy_counter_advance.
 - rewrite C7; exact H7.
 - rewrite Cb; exact Hb.
 - rewrite Cd; exact Hd.
 - rewrite Cl; exact Hl.
 - rewrite Ca; exact Ha.
 - apply copy_iteration_success; try assumption.
   + intros j Hj; rewrite Hd,H5; apply copy_source_domain; assumption.
   + intros j Hj; rewrite Hd,H6; apply copy_destination_domain; assumption.
   + rewrite H5; apply copy_address_alignment; auto.
   + rewrite H6; apply copy_address_alignment; auto.
 - rewrite (copy_iteration_normal_form s Hb),upd_pc_current.
   rewrite H6,H7,copy_counter_advance,copy_branch_bound by exact Hk.
   assert (E : (k <? 4606) = true) by (apply N.ltb_lt; exact Hk).
   rewrite E in Hp; rewrite Hp.
   destruct (N.succ k <? 4606); [reflexivity|vm_compute; reflexivity].
Qed.
Theorem copy_control_all k : k <= 4606 -> CopyControl k (copyState k).
Proof.
 induction k using N.peano_ind; intro Hk.
 - rewrite copy_state_zero; apply copy_control_initial.
 - rewrite copy_state_successor; apply copy_control_step; [lia|apply IHk; lia].
Qed.
Theorem copy_loop_control_endpoint :
 regs (copyState 4606) 5 = n2w (initDataRom+8*4606) /\
 regs (copyState 4606) 6 = n2w initDataEnd /\
 regs (copyState 4606) 7 = n2w initDataEnd /\
 pc (copyState 4606) = n2w 0x8000002c /\
 be (copyState 4606) = false /\ failed (copyState 4606) = false /\
 mem_domain (copyState 4606) = bootstrapDomain /\
 lr (copyState 4606) = 1 /\ align (copyState 4606) = 2.
Proof.
 destruct (copy_control_all 4606 ltac:(lia)) as [H5 H6 H7 Hb Hd Hl Ha Hf Hp].
 split; [exact H5|].
 split; [exact H6|].
 split; [exact H7|].
 split; [exact Hp|].
 split; [exact Hb|].
 split; [exact Hf|].
 split; [exact Hd|].
 split; [exact Hl|exact Ha].
Qed.

Lemma copy_offset_value base offset :
 base = initDataRom \/ base = initDataRam -> offset <= 8*4606+8 ->
 w2n (n2w (base+offset) : word 64) = base+offset.
Proof.
 intros Hb Ho; rewrite w2n_n2w; change (dimword 64) with (2^64).
 apply N.mod_small; destruct Hb as [Hb|Hb]; subst base; copy_numbers; lia.
Qed.
Record CopyBytes (k : N) (s : asm_state 64) : Prop := {
 copied_bytes : forall offset, offset < 8*k ->
  mem s (n2w (initDataRam+offset)) = romMemory (n2w (initDataRom+offset));
 outside_copied : forall x,
  ~ (initDataRam <= w2n x /\ w2n x < initDataRam+8*k) -> mem s x = romMemory x
}.
Lemma copy_source_unchanged k s offset : k <= 4606 -> offset <= 8*4606+8 ->
 CopyBytes k s -> mem s (n2w (initDataRom+offset)) = romMemory (n2w (initDataRom+offset)).
Proof.
 intros Hk Ho [_ Hframe]; apply Hframe.
 rewrite copy_offset_value by (auto; exact Ho); copy_numbers; lia.
Qed.
Theorem copy_bytes_initial : CopyBytes 0 copyEntryAsm.
Proof.
 constructor.
 - intros offset Hoffset; lia.
 - intros x Hout; reflexivity.
Qed.
Theorem copy_bytes_step k s : k < 4606 -> CopyControl k s -> CopyBytes k s ->
 CopyBytes (N.succ k) (copyIteration s).
Proof.
 intros Hk Hcontrol Hbytes.
 destruct Hcontrol as [H5 H6 H7 Hb Hd Hl Ha Hf Hp].
 destruct Hbytes as [Hcopied Hframe].
 constructor.
 - intros offset Hoffset; destruct (N.lt_ge_cases offset (8*k)) as [Hold|Hnew].
   + rewrite copy_iteration_frame by
      (try exact Hb; intros j Hj E; apply (f_equal w2n) in E;
       rewrite H6,copy_address_value in E by (auto; lia);
       rewrite copy_offset_value in E by (auto; lia); lia).
     apply Hcopied; exact Hold.
   + set (j := offset-8*k).
     assert (Hj : j < 8) by (unfold j; lia).
     assert (Eoffset : 8*k+j=offset) by (unfold j; lia).
     replace (n2w (initDataRam+offset) : word 64) with (regs s 6+n2w j)%w.
     2:{ rewrite H6,word_add_n2w; f_equal; lia. }
     rewrite copy_iteration_selected by (exact Hb || exact Hj).
     rewrite H5,word_add_n2w.
     replace (initDataRom+8*k+j) with (initDataRom+offset) by lia.
     apply copy_source_unchanged with (k:=k); [lia|lia|constructor; assumption].
 - intros x Hout.
   rewrite copy_iteration_frame by
    (try exact Hb; intros j Hj E; apply Hout; rewrite E,H6;
     rewrite copy_address_value by (auto; lia); split; lia).
   apply Hframe; intro Hin; apply Hout; destruct Hin as [Hlo Hhi]; split; lia.
Qed.
Theorem copy_bytes_all k : k <= 4606 -> CopyBytes k (copyState k).
Proof.
 induction k using N.peano_ind; intro Hk.
 - rewrite copy_state_zero; apply copy_bytes_initial.
 - rewrite copy_state_successor; apply copy_bytes_step.
   + lia.
   + apply copy_control_all; lia.
   + apply IHk; lia.
Qed.
Theorem copy_loop_bytes_endpoint offset : offset < 8*4606 ->
 mem (copyState 4606) (n2w (initDataRam+offset)) =
 romMemory (n2w (initDataRom+offset)).
Proof.
 intro Ho; exact (copied_bytes 4606 (copyState 4606)
  (copy_bytes_all 4606 ltac:(lia)) offset Ho).
Qed.
Theorem copy_loop_frame_endpoint x :
 ~ (initDataRam <= w2n x /\ w2n x < initDataEnd) ->
 mem (copyState 4606) x = romMemory x.
Proof.
 intro Hout; apply (outside_copied 4606 (copyState 4606)
  (copy_bytes_all 4606 ltac:(lia))); exact Hout.
Qed.
