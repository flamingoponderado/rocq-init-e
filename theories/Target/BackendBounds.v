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

Lemma signed_small_word n : n <= 2040 -> Zs (n2w n : word 64) = Z.of_N n.
Proof.
 intros H; unfold Zs; rewrite w2n_n2w.
 change ((if 9223372036854775808 <=? n mod 18446744073709551616
 then (Z.of_N (n mod 18446744073709551616)-18446744073709551616)%Z
 else Z.of_N (n mod 18446744073709551616)) = Z.of_N n).
 rewrite N.mod_small by lia.
 assert (E : (9223372036854775808 <=? n)=false) by (apply N.leb_gt; lia).
 rewrite E; reflexivity.
Qed.
Theorem stack_allocation_immediate n : n <= stack_remove.max_stack_alloc ->
 asm.valid_imm riscv_target.riscv_config (inl asm.Sub) (n2w (n*8)) = true /\
 asm.valid_imm riscv_target.riscv_config (inl asm.Add) (n2w (n*8)) = true.
Proof.
 intros H; change (n<=255) in H.
 change ((word_lt riscv_target.min12 (n2w (n*8)) && word_le (n2w (n*8)) riscv_target.max12)=true /\
 (word_le riscv_target.min12 (n2w (n*8)) && word_le (n2w (n*8)) riscv_target.max12)=true).
 rewrite !word_lt_Zs,!word_le_Zs.
 rewrite signed_small_word by lia.
 replace (Zs riscv_target.min12) with (-2048)%Z by (vm_compute; reflexivity).
 replace (Zs riscv_target.max12) with 2047%Z by (vm_compute; reflexivity).
 rewrite !Bool.andb_true_iff,!Z.ltb_lt,!Z.leb_le; lia.
Qed.

Lemma signed_negative_small n : n <= 384 ->
 Zs (word_sub (n2w 0) (n2w n) : word 64) = (-Z.of_N n)%Z.
Proof.
 intros H; destruct (N.eq_dec n 0) as [E|E]; [subst n; vm_compute; reflexivity|].
 unfold word_sub; rewrite (proj2 WORD_ADD_0).
 unfold word_2comp,Zs; rewrite !w2n_n2w.
 change ((if 9223372036854775808 <=? (18446744073709551616-n mod 18446744073709551616) mod 18446744073709551616
 then (Z.of_N ((18446744073709551616-n mod 18446744073709551616) mod 18446744073709551616)-18446744073709551616)%Z
 else Z.of_N ((18446744073709551616-n mod 18446744073709551616) mod 18446744073709551616)) = (-Z.of_N n)%Z).
 rewrite (N.mod_small n) by lia.
 rewrite N.mod_small by lia.
 assert (B : (9223372036854775808 <=? 18446744073709551616-n)=true) by (apply N.leb_le; lia).
 rewrite B,N2Z.inj_sub by lia; lia.
Qed.
Theorem stack_store_offset_bounds name :
 asm.addr_offset_ok riscv_target.riscv_config (stack_remove.store_offset name) = true /\
 asm.hw_offset_ok riscv_target.riscv_config (stack_remove.store_offset name) = true.
Proof.
 pose proof (stack_store_position_bound name) as H.
 change (asm.offset_ok 0 (riscv_target.min12,riscv_target.max12)
 (word_sub (n2w 0) (n2w (8*stack_remove.store_pos name)))=true /\
 asm.offset_ok 0 (riscv_target.min12,riscv_target.max12)
 (word_sub (n2w 0) (n2w (8*stack_remove.store_pos name)))=true).
 unfold asm.offset_ok; rewrite !word_le_Zs.
 rewrite signed_negative_small by lia.
 replace (Zs riscv_target.min12) with (-2048)%Z by (vm_compute; reflexivity).
 replace (Zs riscv_target.max12) with 2047%Z by (vm_compute; reflexivity).
 rewrite (proj2 aligned_0).
 rewrite !Bool.andb_true_iff,!Z.leb_le; repeat split; try reflexivity; lia.
Qed.
