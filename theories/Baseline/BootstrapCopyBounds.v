(** Numeric safety obligations for every original bitmap-copy iteration. *)
From Galette Require Import Base.
From Stdlib Require Import NArith Lia.
From Galette.HOL.src.n_bit Require Import words alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list rich_list.
From InitE.InitE Require Import Parameters BaselineArtifactLayout SubmissionModel.
From InitE.Baseline Require Import BootstrapProgram BootstrapMemory BootstrapCodeFacts.
Open Scope N_scope.
Ltac copy_numbers := cbv [initDataRom initDataRam initDataEnd bitmapWordCount
 initialPc codeSizeLimit ramStart ramEnd ramSize inputStart inputEnd inputSize
 outputStart outputEnd outputSize nativePc] in *.
Lemma copy_range_domain (a : word 64) :
 (initDataRom <= w2n a /\ w2n a < initDataRom+8*4617) \/
 (initDataRam <= w2n a /\ w2n a < initDataEnd) -> bootstrapDomain a.
Proof.
 intro Hr; unfold bootstrapDomain; split.
 - unfold submissionMemoryDomain, submissionSharedDomain; split.
   + copy_numbers; lia.
   + copy_numbers; intros [[H1 H2]|[H1 H2]]; lia.
 - intros i Hi E.
   assert (Hin : In i (COUNT_LIST 22)) by (apply bootstrap_count_in; exact Hi).
   assert (Hslot : w2n ((n2w nativePc-n2w (16*(i+1)))%w : word 64) < initDataRom).
   { vm_compute in Hin; repeat destruct Hin as [Hin|Hin]; try contradiction;
     subst i; vm_compute; congruence. }
   rewrite <- E in Hslot; copy_numbers; lia.
Qed.
Lemma copy_address_value base k j :
 base = initDataRom \/ base = initDataRam -> k <= 4617 -> j < 8 ->
 w2n (n2w (base+8*k)+n2w j : word 64)%w = base+8*k+j.
Proof.
 intros Hb Hk Hj; rewrite word_add_n2w,w2n_n2w.
 change (dimword 64) with (2^64); apply N.mod_small.
 destruct Hb as [Hb|Hb]; subst base; copy_numbers; lia.
Qed.
Theorem copy_source_domain k j : k < 4617 -> j < 8 ->
 bootstrapDomain (n2w (initDataRom+8*k)+n2w j)%w.
Proof.
 intros Hk Hj; apply copy_range_domain; left.
 rewrite copy_address_value by (auto; lia); lia.
Qed.
Theorem copy_destination_domain k j : k < 4617 -> j < 8 ->
 bootstrapDomain (n2w (initDataRam+8*k)+n2w j)%w.
Proof.
 intros Hk Hj; apply copy_range_domain; right.
 rewrite copy_address_value by (auto; lia); copy_numbers; lia.
Qed.
Theorem copy_address_alignment base k :
 base = initDataRom \/ base = initDataRam ->
 aligned 3 (n2w (base+8*k) : word 64) = true.
Proof.
 intro Hb; apply MOD_0_aligned.
 change ((base+8*k) mod 8 = 0).
 rewrite N.add_mod,N.mul_mod by discriminate.
 destruct Hb as [Hb|Hb]; subst base; cbv [initDataRom initDataRam];
 rewrite N.mod_same by discriminate; cbn; reflexivity.
Qed.
