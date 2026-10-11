(** Physical memory writes agree with the original Galette machine.
    No alignment or byte-count restriction is imposed on the raw primitive. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From InitE.Target Require Import ReducedTypes ReducedStateOps ReducedMemory
 StateEmbedding StateAgreement InstructionAgreement MemoryAgreement.
Open Scope N_scope.

Theorem write_memory_embedding (s : ReducedTypes.riscv_state)
 (value : word 64) (index : word 61) :
 embedriscv_state (ReducedMemory.writeMEM value index s) =
 riscv.write'MEM (value,index) (embedriscv_state s).
Proof.
 unfold ReducedMemory.writeMEM,riscv.write'MEM.
 cbn beta iota zeta.
 change (63%N) with (dimindex 8+56-1)%N.
 change (55%N) with (dimindex 8+48-1)%N.
 change (47%N) with (dimindex 8+40-1)%N.
 change (39%N) with (dimindex 8+32-1)%N.
 change (31%N) with (dimindex 8+24-1)%N.
 change (23%N) with (dimindex 8+16-1)%N.
 change (15%N) with (dimindex 8+8-1)%N.
 change (7%N) with (dimindex 8+0-1)%N.
 rewrite !extract_shift_resize by (vm_compute; congruence).
 unfold embedriscv_state.
 cbn; rewrite !update_agreement, (proj1 WORD_ADD_0); reflexivity.
Qed.

Theorem raw_write_embedding (s : ReducedTypes.riscv_state)
 (address data : word 64) (nbytes : N) :
 embedriscv_state (ReducedMemory.rawWriteData address data nbytes s) =
 riscv.rawWriteData (address,data,nbytes) (embedriscv_state s).
Proof.
 unfold ReducedMemory.rawWriteData,riscv.rawWriteData.
 replace (w2w (n2w 1 : word 1) : word 64) with (n2w 1 : word 64) by reflexivity.
 assert (Hi : (word_extract 63 3 address : word 61) = w2w (word_lsr address 3)).
 { apply (extract_shift_resize (a:=64) (b:=61) address 3); vm_compute; congruence. }
 assert (Ha : (word_extract 2 0 address : word 3) = w2w address).
 { exact (low_extract_resize (a:=64) (b:=3) address). }
 rewrite !Hi,!Ha.
 cbn beta iota zeta.
 rewrite !word_memory_embedding.
 destruct (bool_decide (w2n (w2w address : word 3)=0)) eqn:H.
 - apply (proj1 (bool_decide_spec _)) in H; rewrite H.
   replace (0 =? 0) with true by reflexivity.
   cbn beta iota zeta.
   rewrite write_memory_embedding; reflexivity.
 - assert (Hn : (w2n (w2w address : word 3) =? 0)=false).
   { apply N.eqb_neq; intro E; assert (bool_decide (w2n (w2w address : word 3)=0)=true) by (apply (proj2 (bool_decide_spec _)); exact E); congruence. }
   rewrite Hn.
   change (word_len (word_sub (word_lsl (n2w 1 : word 64) (nbytes*8)) (n2w 1))) with 64.
   change (word_len data) with 64.
   change (64 / 8) with 8.
   destruct (w2n (w2w address : word 3)+nbytes <=? 8).
   + rewrite write_memory_embedding; reflexivity.
   + change (64-1)%N with (dimindex 64-1)%N.
     rewrite low_extract_resize.
     change (2*64-1)%N with (dimindex 64+64-1)%N.
     rewrite extract_shift_resize by (vm_compute; congruence).
     rewrite !write_memory_embedding; reflexivity.
Qed.
