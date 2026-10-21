(** Original BootstrapCodeFacts.lean: actual encoded bootstrap blocks are in
    the literal ROM and executable domain. No installation state is assumed. *)
From Galette Require Import Base.
From Stdlib Require Import List NArith Lia.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.relation Require Import relation.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From InitE.Guest Require Import Basic.
From InitE.InitE Require Import Parameters BaselineArtifactLayout SubmissionModel.
From InitE.Baseline Require Import Artifacts ArtifactFacts BootstrapProgram BootstrapMemory BootstrapSteps BootstrapPrefix.
Open Scope N_scope.

Theorem bootstrap_code_domain (a : word 64) :
 initialPc <= w2n a -> w2n a < initialPc+208 -> bootstrapDomain a.
Proof.
 intros Hlo Hhi; unfold bootstrapDomain; split.
 - unfold submissionMemoryDomain, submissionSharedDomain; split.
   + left; unfold codeSizeLimit in *; split; lia.
   + cbv [initialPc inputStart inputEnd inputSize outputStart outputEnd outputSize] in *.
     intros [[H1 H2]|[H1 H2]]; lia.
 - intros i Hi E.
   assert (Hcases : In i (COUNT_LIST 4)) by (vm_compute; lia).
   assert (Hslot : initialPc+208 < w2n ((n2w nativePc-n2w (16*(i+1)))%w : word 64)).
   { vm_compute in Hcases; repeat destruct Hcases as [Hcases|Hcases]; try contradiction;
     subst i; vm_compute; congruence. }
   rewrite <- E in Hslot; lia.
Qed.

Lemma bootstrap_nth_take {A} (xs : list A) i count (fallback : A) :
 i < count -> nthN i (TAKE count xs) fallback = nthN i xs fallback.
Proof.
 intros Hi; rewrite !nthN_eq_nth, TAKE_firstn, nth_firstn.
 assert (Hnat : (N.to_nat i <? N.to_nat count)%nat = true)
  by (apply Nat.ltb_lt; lia).
 rewrite Hnat; reflexivity.
Qed.

Theorem bootstrap_rom_prefix (a : word 64) :
 initialPc <= w2n a -> w2n a < initialPc+208 ->
 romMemory a = nthN (w2n a-initialPc) originalBootstrapBytes (n2w 0).
Proof.
 intros Hlo Hhi.
 pose proof (proj2 (proj2 (proj2 original_literal_sizes))) as Hlength.
 unfold romMemory; rewrite Hlength.
 assert (Hguard : (initialPc <=? w2n a) && (w2n a <? initialPc+fullRomByteCount) = true).
 { apply andb_true_iff; split; [apply N.leb_le; exact Hlo|].
   apply N.ltb_lt; unfold fullRomByteCount; lia. }
 rewrite Hguard.
 rewrite <- bootstrap_bytes_match, <- encoded_bootstrap_in_rom.
 symmetry; apply bootstrap_nth_take; lia.
Qed.

Theorem bootstrap_block_ranges :
 forallb (fun block => (initialPc <=? fst block) &&
  (fst block+LENGTH (riscv_target.riscv_enc (snd block)) <=? initialPc+208)) bootstrapBlocks = true.
Proof. vm_compute; reflexivity. Qed.

Theorem bootstrap_block_bytes :
 forallb (fun block => forallb (fun offset =>
  bool_decide (nthN (fst block+offset-initialPc) originalBootstrapBytes (n2w 0) =
   nthN offset (riscv_target.riscv_enc (snd block)) (n2w 0)))
  (COUNT_LIST (LENGTH (riscv_target.riscv_enc (snd block))))) bootstrapBlocks = true.
Proof. vm_compute; reflexivity. Qed.

Lemma bootstrap_count_in n i : i < n -> In i (COUNT_LIST n).
Proof.
 revert i; induction n using N.peano_ind; intros i Hi; [lia|].
 change (In i (COUNT_LIST (SUC n))); rewrite (proj2 (COUNT_LIST_def n)).
 destruct (N.eq_dec i 0) as [E|E].
 - subst i; left; reflexivity.
 - right; apply in_map_iff; exists (i-1); split.
   + lia.
   + apply IHn; lia.
Qed.

Lemma bootstrap_word_advance (pc : word 64) n :
 (pc+n2w 1+n2w n)%w = (pc+n2w (SUC n))%w.
Proof.
 rewrite <- WORD_ADD_ASSOC, word_add_n2w.
 replace (1+n) with (SUC n) by lia; reflexivity.
Qed.

Lemma bytes_of_offsets (bytes : list (word 8)) (pc : word 64)
 (memory : word 64 -> word 8) (domain : word 64 -> Prop) :
 (forall n, n < LENGTH bytes -> memory (pc+n2w n)%w = nthN n bytes (n2w 0)) ->
 (forall n, n < LENGTH bytes -> domain (pc+n2w n)%w) ->
 bytes_in_memory pc bytes memory domain.
Proof.
 revert pc; induction bytes as [|byte rest IH]; intros pc Hbytes Hdomain; cbn [bytes_in_memory].
 - exact I.
 - split.
   + specialize (Hbytes 0 ltac:(cbn [LENGTH]; lia)).
     rewrite (proj1 WORD_ADD_0) in Hbytes; exact Hbytes.
   + split.
     * specialize (Hdomain 0 ltac:(cbn [LENGTH]; lia)).
       rewrite (proj1 WORD_ADD_0) in Hdomain; exact Hdomain.
     * apply IH.
       -- intros n Hn; rewrite bootstrap_word_advance.
          specialize (Hbytes (SUC n) ltac:(cbn [LENGTH]; lia)).
          cbn [nthN] in Hbytes.
          assert (Hz : (SUC n =? 0) = false) by (apply N.eqb_neq; lia).
          rewrite Hz in Hbytes; replace (SUC n-1) with n in Hbytes by (lia).
          exact Hbytes.
       -- intros n Hn; rewrite bootstrap_word_advance; apply Hdomain; cbn [LENGTH]; lia.
Qed.

Theorem block_bytes (block : N * asm.asm 64) : In block bootstrapBlocks ->
 bytes_in_memory (n2w (fst block)) (riscv_target.riscv_enc (snd block)) romMemory bootstrapDomain.
Proof.
 intros Hin.
 pose proof bootstrap_block_ranges as Hranges; rewrite forallb_forall in Hranges.
 specialize (Hranges block Hin); apply andb_true_iff in Hranges as [Hlo Hhi].
 apply N.leb_le in Hlo; apply N.leb_le in Hhi.
 pose proof bootstrap_block_bytes as Hbytes; rewrite forallb_forall in Hbytes.
 specialize (Hbytes block Hin); rewrite forallb_forall in Hbytes.
 assert (Haddress : forall n, n < LENGTH (riscv_target.riscv_enc (snd block)) ->
  w2n ((n2w (fst block)+n2w n)%w : word 64) = fst block+n).
 { intros n Hn; rewrite word_add_n2w, w2n_n2w.
   apply N.mod_small; change (fst block+n < 2^64).
   unfold initialPc in Hhi; lia. }
 apply bytes_of_offsets.
 - intros n Hn; rewrite bootstrap_rom_prefix.
   + rewrite (Haddress n Hn); apply (proj1 (bool_decide_spec _)).
     apply Hbytes; apply bootstrap_count_in; exact Hn.
   + rewrite (Haddress n Hn); lia.
   + rewrite (Haddress n Hn); lia.
 - intros n Hn; apply bootstrap_code_domain; rewrite (Haddress n Hn); lia.
Qed.

Theorem bootstrap_block_bounds (block : N * asm.asm 64) : In block bootstrapBlocks ->
 initialPc <= fst block /\ fst block+LENGTH (riscv_target.riscv_enc (snd block)) <= initialPc+208.
Proof.
 pose proof bootstrap_block_ranges as H; rewrite forallb_forall in H.
 intros Hin; specialize (H block Hin); apply andb_true_iff in H as [Hlo Hhi].
 split; apply N.leb_le; assumption.
Qed.

Lemma checked_loc (s : asm_state 64) reg addressPc address :
 In (addressPc,bootLoc reg addressPc address) bootstrapBlocks ->
 pc s = n2w addressPc -> mem s = romMemory -> mem_domain s = bootstrapDomain ->
 lr s = 1 -> be s = false -> align s = 2 -> ~ failed s ->
 asm_step riscv_target.riscv_config s (bootLoc reg addressPc address)
  (after s (bootLoc reg addressPc address)).
Proof.
 intros Hin Hpc Hmem Hdomain Hlr Hbe Halign Hfailed; apply checked_step.
 - rewrite Hpc,Hmem,Hdomain; exact (block_bytes _ Hin).
 - exact Hlr.
 - exact Hbe.
 - exact Halign.
 - change (~ failed s); exact Hfailed.
 - pose proof bootstrap_instructions_admitted as H.
   change (forallb (fun block => asm_ok (snd block) riscv_target.riscv_config) bootstrapBlocks = true) in H.
   rewrite forallb_forall in H; exact (H _ Hin).
Qed.

Theorem prefix_checked : Checked prefixCode initialAsm.
Proof.
 cbn [prefixCode bootstrapBlocks TAKE MAP Checked].
 split.
 - apply checked_loc.
   + unfold bootstrapBlocks; left; reflexivity.
   + reflexivity.
   + reflexivity.
   + reflexivity.
   + reflexivity.
   + reflexivity.
   + reflexivity.
   + intro H; discriminate H.
 - split.
   + apply checked_loc.
     * unfold bootstrapBlocks; right; left; reflexivity.
     * reflexivity.
     * reflexivity.
     * reflexivity.
     * reflexivity.
     * reflexivity.
     * reflexivity.
     * intro H; discriminate H.
   + split.
     * apply checked_loc.
       -- unfold bootstrapBlocks; right; right; left; reflexivity.
       -- reflexivity.
       -- reflexivity.
       -- reflexivity.
       -- reflexivity.
       -- reflexivity.
       -- reflexivity.
       -- intro H; discriminate H.
     * exact I.
Qed.

Theorem prefix_checked_trace :
 RTC (fun before after => exists i,
  asm_step riscv_target.riscv_config before i after) initialAsm copyEntryAsm.
Proof.
 rewrite <- prefix_endpoint; apply checked_trace; exact prefix_checked.
Qed.
