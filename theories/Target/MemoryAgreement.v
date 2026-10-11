(** Physical memory primitive agreement for the original reduced machine. *)
From Galette Require Import Base.
From Stdlib Require Import Lia.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import fcp_defs lemmas.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From InitE.Target Require Import ReducedTypes ReducedMemory StateEmbedding StateAgreement InstructionAgreement.
Open Scope N_scope.
Lemma extract_shift_resize {a b} (w : word a) l :
 dimindex b + l <= dimindex a ->
 (word_extract (dimindex b + l - 1) l w : word b) = w2w (word_lsr w l).
Proof.
 intros H; unfold word_extract; cbn.
 apply word_bit_ext; intros i Hi.
 rewrite !fcp_index_w2w by exact Hi.
 assert (Ha : i < dimindex a) by lia.
 rewrite fcp_index_word_bits, fcp_index_word_lsr by exact Ha.
 assert (Hia : (i <? dimindex a) = true) by (apply N.ltb_lt; exact Ha).
 assert (Hshift : (i+l <? dimindex a) = true) by (apply N.ltb_lt; lia).
 assert (Hbits : (i+l <=? MIN (dimindex b+l-1) (dimindex a-1)) = true).
 { apply N.leb_le; unfold MIN; destruct (dimindex b+l-1 <? dimindex a-1); lia. }
 rewrite Hia,Hshift,Hbits; reflexivity.
Qed.
Theorem raw_read_embedding (s : ReducedTypes.riscv_state) address :
 riscv.rawReadData address (embedriscv_state s) = ReducedMemory.rawReadData address s.
Proof.
 unfold riscv.rawReadData,ReducedMemory.rawReadData.
 change (63%N) with (dimindex 61+3-1)%N at 1.
 rewrite extract_shift_resize by (vm_compute; congruence).
 change (2%N) with (dimindex 3-1)%N.
 rewrite low_extract_resize.
 cbn beta iota zeta.
 rewrite !word_memory_embedding.
 destruct (bool_decide (w2n (w2w address : word 3)=0)) eqn:H.
 - apply (proj1 (bool_decide_spec _)) in H; rewrite H; reflexivity.
 - assert (Hn : (w2n (w2w address : word 3) =? 0)=false).
   { apply N.eqb_neq; intro E; assert (bool_decide (w2n (w2w address : word 3)=0)=true) by (apply (proj2 (bool_decide_spec _)); exact E); congruence. }
   rewrite Hn; change (63%N) with (dimindex 64-1)%N; rewrite low_extract_resize; reflexivity.
Qed.

Definition physical_mode (s : ReducedTypes.riscv_state) : Prop :=
 ReducedTypes.mstatus_VM (ReducedTypes.MachineCSR_mstatus
 (ReducedStateOps.MCSR s)) = n2w 0.
Theorem validity_physical_mode s : Configuration.riscvOk s = true -> physical_mode s.
Proof.
 unfold Configuration.riscvOk,physical_mode,ReducedStateOps.MCSR.
 rewrite !Bool.andb_true_iff; intros [[[[Hv Ha] Hf] He] Hp].
 apply (proj1 (bool_decide_spec _)); exact Hv.
Qed.
Theorem translate_physical s address ft ac :
 physical_mode s ->
 riscv.translateAddr (address,ft,ac) (embedriscv_state s) = (Some address,embedriscv_state s).
Proof.
 intros H.
 assert (Hv : riscv.mstatus_VM (riscv.MachineCSR_mstatus (riscv.MCSR (embedriscv_state s))) = n2w 0) by exact H.
 unfold riscv.translateAddr; rewrite Hv.
 unfold riscv.vmType.
 assert (Hz : bool_decide ((n2w 0 : word 5)=n2w 0)=true) by (apply (proj2 (bool_decide_spec _)); reflexivity).
 rewrite Hz.
 reflexivity.
Qed.
