(** Signed immediate and offset bounds for the fixed RISC-V backend. *)
From Galette Require Import Base.
From Stdlib Require Import Lia.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.compiler.backend Require stack_remove.
From Galette.HOL.src.n_bit Require Import words alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.cakeml.compiler.encoders.asm Require asm.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
Open Scope N_scope.
Theorem small_byte_offset (w : word 64) :
 word_le (word_2comp (n2w 8)) w = true -> word_le w (n2w 8) = true ->
 asm.byte_offset_ok riscv_target.riscv_config w = true.
Proof.
 intros Hl Hu; rewrite word_le_Zs in Hl,Hu.
 change ((-8 <=? Zs w)%Z = true) in Hl.
 change ((Zs w <=? 8)%Z = true) in Hu.
 apply Z.leb_le in Hl,Hu.
 change (asm.offset_ok 0 (riscv_target.min12,riscv_target.max12) w = true).
 unfold asm.offset_ok.
 rewrite !word_le_Zs.
 replace (Zs riscv_target.min12) with (-2048)%Z by (vm_compute; reflexivity).
 replace (Zs riscv_target.max12) with 2047%Z by (vm_compute; reflexivity).
 replace (aligned 0 w) with true by (symmetry; apply (proj2 aligned_0)).
 rewrite !Bool.andb_true_iff; repeat split; try reflexivity; apply Z.leb_le; lia.
Qed.

Lemma index_find_bound {A} (P : A -> bool) xs : forall initial index value,
 INDEX_FIND initial P xs = Some (index,value) -> index < initial + LENGTH xs.
Proof.
 induction xs as [|head tail IH]; intros initial index value H; cbn [INDEX_FIND] in H; [discriminate|].
 destruct (P head).
 - injection H as E _; subst index; cbn [LENGTH]; lia.
 - specialize (IH _ _ _ H); cbn [LENGTH]; change (index < N.succ initial + LENGTH tail) in IH.
   change (index < initial + N.succ (LENGTH tail)); lia.
Qed.
Theorem stack_store_position_bound name : stack_remove.store_pos name <= 48.
Proof.
 unfold stack_remove.store_pos.
 destruct (INDEX_FIND 0 (fun n => bool_decide (n=name)) stack_remove.store_list) as [[index value]|] eqn:H.
 - pose proof (index_find_bound _ _ _ _ _ H) as Hb.
   change (index < 0+48) in Hb; lia.
 - lia.
Qed.
