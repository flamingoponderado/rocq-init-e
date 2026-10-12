(** Original compiler data/shared domains at the actual native entry. *)
From Galette Require Import Base.
From Stdlib Require Import NArith Lia.
From Galette.HOL.src.n_bit Require Import words byte alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import inst.
From InitE.InitE Require Import Parameters BaselineArtifactLayout SubmissionModel SourceSemantics.
From InitE.Baseline Require Import BootstrapMemory BootstrapCodeFacts BitmapSeparation PackedWordMemory NativeCodeInstallation ArtifactFacts Artifacts.
Open Scope N_scope.
Definition baselineHeapStackDomain (a : word 64) : Prop := sourceBase <= w2n a /\ w2n a < ramEnd.
Definition baselineDataDomain : word 64 -> Prop := baselineHeapStackDomain UNION baselineBitmapByteDomain.
Lemma byte_align_value (a : word 64) : w2n (byte_align a) = w2n a/8*8.
Proof.
 change (w2n (align 3 a) = w2n a/8*8).
 rewrite align_w2n,w2n_n2w; change ((w2n a/8*8) mod (2^64) = w2n a/8*8).
 apply N.mod_small.
 pose proof (w2n_lt a) as Hbound; change (w2n a < 2^64) in Hbound.
 pose proof (N.div_mod (w2n a) 8 ltac:(discriminate)); lia.
Qed.
Lemma byte_align_range_closed low high (a : word 64) : high mod 8 = 0 ->
 low <= w2n (byte_align a) -> w2n (byte_align a) < high ->
 low <= w2n a /\ w2n a < high.
Proof.
 intros Hhigh Hlo Hhi; rewrite byte_align_value in Hlo,Hhi.
 pose proof (N.div_mod (w2n a) 8 ltac:(discriminate)).
 pose proof (N.mod_lt (w2n a) 8 ltac:(discriminate)).
 pose proof (N.div_mod high 8 ltac:(discriminate)).
 split; lia.
Qed.
Theorem baseline_heap_domain_closed a : baselineHeapStackDomain (byte_align a) -> baselineHeapStackDomain a.
Proof.
 intros [Hlo Hhi]; unfold baselineHeapStackDomain; apply byte_align_range_closed; [vm_compute; reflexivity|exact Hlo|exact Hhi].
Qed.
Theorem baseline_data_domain_closed a : baselineDataDomain (byte_align a) -> baselineDataDomain a.
Proof.
 intros [Hheap|Hbitmap].
 - left; apply baseline_heap_domain_closed; exact Hheap.
 - right; apply baseline_bitmap_domain_closed; exact Hbitmap.
Qed.
Theorem baseline_shared_domain_closed a : submissionSharedDomain (byte_align a) -> submissionSharedDomain a.
Proof.
 intros [[Hlo Hhi]|[Hlo Hhi]].
 - left; apply byte_align_range_closed; [vm_compute; reflexivity|exact Hlo|exact Hhi].
 - right; apply byte_align_range_closed; [vm_compute; reflexivity|exact Hlo|exact Hhi].
Qed.
Theorem baseline_heap_domain_subset : baselineHeapStackDomain SUBSET bootstrapDomain.
Proof.
 intros a [Hlo Hhi]; unfold bootstrapDomain; split.
 - unfold submissionMemoryDomain,submissionSharedDomain; split.
   + right; cbv [sourceBase ramStart] in *; split; lia.
   + cbv [sourceBase inputStart inputEnd inputSize outputStart outputEnd outputSize] in *.
     intros [[H1 H2]|[H1 H2]]; lia.
 - intros i Hi E.
   assert (Hin : In i (COUNT_LIST 22)) by (apply bootstrap_count_in; exact Hi).
   assert (Hslot : w2n ((n2w nativePc-n2w (16*(i+1)))%w : word 64) < sourceBase).
   { vm_compute in Hin; repeat destruct Hin as [Hin|Hin]; try contradiction; subst i; vm_compute; congruence. }
   rewrite <- E in Hslot; lia.
Qed.
Theorem baseline_data_domain_subset : baselineDataDomain SUBSET bootstrapDomain.
Proof. intros a [Hheap|Hbitmap]; [apply baseline_heap_domain_subset; exact Hheap|apply baseline_bitmap_domain_subset; exact Hbitmap]. Qed.
Theorem baseline_program_shared_disjoint : DISJOINT bootstrapDomain submissionSharedDomain.
Proof. apply DISJOINT_iff; intros a [[[Hmem Hnot] Hslots] Hshared]; exact (Hnot Hshared). Qed.
Theorem baseline_source_shared_domain : sharedDomain = submissionSharedDomain INTER (fun a : word 64 => byte_aligned a).
Proof.
 apply set_ext; intro a; unfold sharedDomain,pred_set.INTER; change ((aligned 3 a = true /\ submissionSharedDomain a) <-> (submissionSharedDomain a /\ aligned 3 a = true)); tauto.
Qed.
Theorem native_byte_data_excluded offset : offset <= 904816 ->
 ~ baselineDataDomain (n2w nativePc+n2w offset)%w.
Proof.
 intros Ho [Hheap|Hbitmap].
 - change (sourceBase <= w2n (n2w nativePc+n2w offset : word 64)%w /\ w2n (n2w nativePc+n2w offset : word 64)%w < ramEnd) in Hheap; rewrite (native_address_value offset Ho) in Hheap;
   cbv [sourceBase nativePc] in *; lia.
 - apply baseline_bitmap_code_disjoint with (a:=(n2w nativePc+n2w offset)%w); [exact Hbitmap|].
   rewrite native_address_value by exact Ho; cbv [initialPc codeSizeLimit nativePc] in *; split; lia.
Qed.
Theorem baseline_code_buffer n : n < 620 ->
 bootstrapDomain (n2w (n+LENGTH nativeCode)+n2w nativePc)%w /\
 ~ baselineDataDomain (n2w (n+LENGTH nativeCode)+n2w nativePc)%w.
Proof.
 intro Hn; rewrite WORD_ADD_COMM; pose proof native_literal_length as Hlength; rewrite Hlength.
 split.
 - apply native_code_buffer_domain; rewrite native_address_value by lia; cbv [nativePc codeBufferLimit]; lia.
 - apply native_byte_data_excluded; lia.
Qed.
Theorem baseline_code_size_bound : 620+LENGTH nativeCode < dimword 64.
Proof. rewrite native_literal_length; vm_compute; congruence. Qed.
