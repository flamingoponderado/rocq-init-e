(** Complete word witnesses for arbitrary byte memories.
    Original MachineWordMemory.lean interfaces, using Galette's proved
    little-endian eight-byte read rather than a new machine-memory model. *)
From Galette Require Import Base.
From Stdlib Require Import NArith Lia.
From Galette.HOL.src.n_bit Require Import words byte alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From Galette.cakeml.compiler.backend Require Import wordLang.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import inst.
From InitE.Guest Require Import Basic.
From InitE.Baseline Require Import BootstrapCopy.
Open Scope N_scope.

(** The auxiliary reader has a total domain. Its state is only a byte-packing
    implementation: it imposes no condition on the memory being witnessed. *)
Definition packedReadState (memory : word 64 -> word 8) : asm_state 64 :=
 mk_asm_state (fun _ => n2w 0) (fun _ => n2w 0) memory (fun _ => True)
  (n2w 0) 1 2 false false.
Definition packedMemoryWord (memory : word 64 -> word 8) (address : word 64) : word 64 :=
 fst (read_mem_word (byte_align address) 8 (packedReadState memory)).
Definition packedWordMemory (memory : word 64 -> word 8) (address : word 64) : wordLang.word_loc 64 :=
 wordLang.Word (packedMemoryWord memory address).

Theorem packedMemoryWord_lane memory address j : j < 8 ->
 (w2w (packedMemoryWord memory address >>> (8*j))%w : word 8) =
 memory (byte_align address+n2w j)%w.
Proof.
 intro Hj; unfold packedMemoryWord.
 exact (read_selected_byte (packedReadState memory) (byte_align address) j eq_refl Hj).
Qed.
Lemma packed_byte_align_twice (address : word 64) : byte_align (byte_align address) = byte_align address.
Proof. unfold byte_align; apply align_align. Qed.
Theorem packedMemoryWord_align memory address :
 packedMemoryWord memory (byte_align address) = packedMemoryWord memory address.
Proof. unfold packedMemoryWord; rewrite packed_byte_align_twice; reflexivity. Qed.
Local Opaque packedMemoryWord.

Theorem packedMemoryWord_byte memory address :
 byte.get_byte address (packedMemoryWord memory address) false = memory address.
Proof.
 unfold byte.get_byte,byte_index; change (dimindex 64 / 8) with 8; cbn beta zeta iota.
 rewrite packedMemoryWord_lane by (apply N.mod_lt; discriminate).
 rewrite byte_align_64_eq by reflexivity; reflexivity.
Qed.
Theorem packedMemoryWord_of_bytes memory (address value : word 64) :
 byte_aligned address = true ->
 (forall j, j < 8 -> memory (address+n2w j)%w = byte.get_byte (n2w j) value false) ->
 packedMemoryWord memory address = value.
Proof.
 intros Ha Hbytes; apply (word_eq_of_get_byte _ _ false).
 - split; [change (8 <= 64); lia|exists 8; reflexivity].
 - intros j Hj; change (j < 8) in Hj.
   assert (Haligned : byte_align address = address) by (apply (proj1 (byte_align_aligned address)); exact Ha).
   unfold byte.get_byte at 1; rewrite byte_index_n2w_le by exact Hj.
   rewrite packedMemoryWord_lane by exact Hj; rewrite Haligned; apply Hbytes; exact Hj.
Qed.
Theorem packedWordMemory_align memory address :
 packedWordMemory memory (byte_align address) = packedWordMemory memory address.
Proof. unfold packedWordMemory; rewrite packedMemoryWord_align; reflexivity. Qed.
Theorem packedWordMemory_of_bytes memory (address value : word 64) :
 byte_aligned address = true ->
 (forall j, j < 8 -> memory (address+n2w j)%w = byte.get_byte (n2w j) value false) ->
 packedWordMemory memory address = wordLang.Word value.
Proof.
 intros Ha Hb; unfold packedWordMemory; rewrite (packedMemoryWord_of_bytes memory address value Ha Hb); reflexivity.
Qed.

(** Exactly the complete data-memory conjunct of [good_init_state]. No domain,
    finiteness, or accessibility restriction is placed on the address. *)
Theorem packedWordMemory_certificate memory address :
 exists value, memory address = byte.get_byte address value false /\
 packedWordMemory memory (byte_align address) = wordLang.Word value.
Proof.
 exists (packedMemoryWord memory address); apply conj.
 - symmetry; apply packedMemoryWord_byte.
 - unfold packedWordMemory; rewrite packedMemoryWord_align; reflexivity.
Qed.
Theorem packed_word_memory_exists (memory : word 64 -> word 8) :
 exists m : word 64 -> wordLang.word_loc 64, forall address, exists value,
 memory address = byte.get_byte address value false /\ m (byte_align address) = wordLang.Word value.
Proof. exists (packedWordMemory memory); intro address; apply packedWordMemory_certificate. Qed.
Theorem packed_good_init_word_witness (s : asm_state 64) : forall address, exists value,
 mem s address = byte.get_byte address value (big_endian riscv_target.riscv_config) /\
 packedWordMemory (mem s) (byte_align address) = wordLang.Word value.
Proof. intro address; exact (packedWordMemory_certificate (mem s) address). Qed.

(** These pointwise literal interfaces also work through word-address wrapping;
    they do not assume a finite support or a bound on the list's length. *)
Lemma packed_address_advance (address : word 64) j :
 (address+n2w 1+n2w j)%w = (address+n2w (N.succ j))%w.
Proof.
 rewrite <- WORD_ADD_ASSOC,word_add_n2w; replace (1+j) with (N.succ j) by lia; reflexivity.
Qed.
Lemma packed_nth_successor {A} j (head : A) rest fallback :
 nthN (N.succ j) (head::rest) fallback = nthN j rest fallback.
Proof.
 cbn [nthN]; assert (Hz : (N.succ j =? 0) = false) by (apply N.eqb_neq; lia).
 rewrite Hz; replace (N.succ j-1) with j by lia; reflexivity.
Qed.
Theorem read_bytearray_literal (address : word 64) (bytes : list (word 8)) reader :
 (forall j, j < LENGTH bytes -> reader (address+n2w j)%w = Some (nthN j bytes (n2w 0))) ->
 read_bytearray address (LENGTH bytes) reader = Some bytes.
Proof.
 revert address; induction bytes as [|head rest IH]; intros address Hbytes.
 - reflexivity.
 - change (LENGTH (head::rest)) with (N.succ (LENGTH rest)).
   rewrite (proj2 (read_bytearray_def address reader (LENGTH rest))).
   pose proof (Hbytes 0 ltac:(cbn [LENGTH]; lia)) as Hhead.
   rewrite (proj1 WORD_ADD_0) in Hhead; change (reader address = Some head) in Hhead.
   rewrite Hhead; rewrite IH; [reflexivity|].
   intros j Hj; rewrite packed_address_advance.
   specialize (Hbytes (N.succ j) ltac:(cbn [LENGTH]; lia)); rewrite packed_nth_successor in Hbytes; exact Hbytes.
Qed.
Theorem bytes_in_mem_literal (address : word 64) (bytes : list (word 8)) memory domain excluded :
 (forall j, j < LENGTH bytes -> domain (address+n2w j)%w /\ ~ excluded (address+n2w j)%w /\
  memory (address+n2w j)%w = nthN j bytes (n2w 0)) ->
 bytes_in_mem address bytes memory domain excluded.
Proof.
 revert address; induction bytes as [|head rest IH]; intros address Hbytes; cbn [bytes_in_mem].
 - constructor.
 - pose proof (Hbytes 0 ltac:(cbn [LENGTH]; lia)) as Hhead.
   rewrite (proj1 WORD_ADD_0) in Hhead; change (domain address /\ ~ excluded address /\ memory address = head) in Hhead.
   destruct Hhead as [Hd [Hex Hvalue]].
   apply conj; [exact Hd|]. apply conj; [exact Hex|]. apply conj; [exact Hvalue|]. apply IH.
   intros j Hj; rewrite packed_address_advance.
   specialize (Hbytes (N.succ j) ltac:(cbn [LENGTH]; lia)); rewrite packed_nth_successor in Hbytes; exact Hbytes.
Qed.
