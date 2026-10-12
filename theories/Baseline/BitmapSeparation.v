(** Original bitmap separation assertion over the actual installed byte memory.
    No input-dependent or concrete-memory premise is required. *)
From Galette Require Import Base.
From Stdlib Require Import List NArith Lia.
From Galette.HOL.src.n_bit Require Import words byte alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.examples.machine_code.hoare_triple Require Import set_sep.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.backend Require Import wordLang.
From Galette.cakeml.compiler.backend.proofs Require Import stack_removeProof.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import inst.
From InitE.Guest Require Import Basic.
From InitE.InitE Require Import Parameters BaselineArtifactLayout SubmissionModel.
From InitE.Baseline Require Import Artifacts ArtifactFacts BootstrapMemory
 BootstrapCopyBounds PackedWordMemory BitmapInstallation.
Open Scope N_scope.
Local Opaque code bitmaps installedMemory packedWordMemory.

Lemma bitmap_map_length {A B} (f : A -> B) values : LENGTH (MAP f values) = LENGTH values.
Proof. rewrite !LENGTH_length,length_map; reflexivity. Qed.

Theorem word_list_graph {B} `{Inhabited B} (values : list B)
 (base : word 64) (memory : word 64 -> B) :
 w2n base + LENGTH values * 8 < dimword 64 ->
 (forall i, i < LENGTH values -> memory (base+n2w i*bytes_in_word)%w = EL i values) ->
 word_list base values (fun2set (memory, addresses base (LENGTH values))).
Proof.
 intros Hb Hmem; rewrite word_list_seteq by (split; [right; reflexivity|exact Hb]).
 apply set_ext; intros entry; unfold fun2set; cbn beta iota zeta.
 change ((exists address, entry = (address,memory address) /\ addresses base (LENGTH values) address) <->
  entry IN list_to_set.LIST_TO_SET (GENLIST (fun i => ((base+n2w i*bytes_in_word)%w, EL i values)) (LENGTH values))).
 rewrite list_to_set.IN_set,In_GENLIST_iff; split.
 - intros [address [He Ha]]; rewrite addresses_thm in Ha; destruct Ha as [i [-> Hi]].
   exists i; split; [exact Hi|]; rewrite <- Hmem by exact Hi; exact He.
 - intros [i [Hi He]]; exists (base+n2w i*bytes_in_word)%w; split.
   + rewrite Hmem by exact Hi; exact He.
   + rewrite addresses_thm; exists i; auto.
Qed.

Theorem word_list_exists_zero {B} (base : word 64) :
 @word_list_exists 64 B base 0 (fun _ => False).
Proof. rewrite (proj1 (word_list_exists_thm base 0)); reflexivity. Qed.

Lemma bitmap_word_address i :
 (n2w (initDataRam+24)+n2w i*bytes_in_word : word 64)%w = n2w (initDataRam+24+8*i).
Proof.
 change (bytes_in_word : word 64) with (n2w 8 : word 64).
 rewrite word_mul_n2w,word_add_n2w; f_equal; lia.
Qed.
Lemma bitmap_word_list_bound :
 w2n (n2w (initDataRam+24) : word 64)+LENGTH (MAP (@Word 64) bitmaps)*8 < dimword 64.
Proof.
 rewrite bitmap_map_length; pose proof (proj1 (proj2 original_literal_sizes)) as Hsize.
 change (LENGTH bitmaps = 4614) in Hsize; rewrite Hsize; vm_compute; reflexivity.
Qed.
Lemma bitmap_word_list_value i : i < LENGTH (MAP (@Word 64) bitmaps) ->
 packedWordMemory installedMemory (n2w (initDataRam+24)+n2w i*bytes_in_word)%w =
 EL i (MAP (@Word 64) bitmaps).
Proof.
 intro Hi; rewrite bitmap_map_length in Hi; rewrite bitmap_word_address.
 rewrite installed_bitmap_word_location by exact Hi.
 rewrite EL_map_N by exact Hi; f_equal.
 rewrite EL_nth by exact Hi; rewrite nthN_eq_nth.
 apply nth_indep; rewrite LENGTH_length in Hi; lia.
Qed.

Lemma bitmap_split_empty {A} (s : A -> Prop) : SPLIT s (s, (fun _ => False)).
Proof. unfold SPLIT; split; sets. Qed.

Theorem baseline_bitmap_separation :
 STAR (word_list (n2w (initDataRam+24)) (MAP (@Word 64) bitmaps))
  (word_list_exists (n2w initDataEnd) 0)
  (fun2set (packedWordMemory installedMemory,
    addresses (n2w (initDataRam+24)) (LENGTH bitmaps))).
Proof.
 exists (fun2set (packedWordMemory installedMemory,
    addresses (n2w (initDataRam+24)) (LENGTH bitmaps))), (fun _ => False).
 split.
 - apply bitmap_split_empty.
 - split; [|apply word_list_exists_zero].
   rewrite <- (bitmap_map_length (@Word 64) bitmaps).
   apply word_list_graph; [apply bitmap_word_list_bound|apply bitmap_word_list_value].
Qed.

(** The bitmap resource consists of aligned word addresses. Its byte lanes
    remain in the ordinary machine domain and outside the other RAM resources. *)
Definition baselineBitmapDomain : word 64 -> Prop :=
 addresses (n2w (initDataRam+24)) (LENGTH bitmaps).
Lemma baseline_bitmap_address a : baselineBitmapDomain a <->
 exists i, i < LENGTH bitmaps /\ a = n2w (initDataRam+24+8*i).
Proof.
 unfold baselineBitmapDomain; rewrite addresses_thm; split;
 intros [i [H1 H2]]; exists i; rewrite bitmap_word_address in *; auto.
Qed.
Lemma baseline_bitmap_aligned a : baselineBitmapDomain a -> byte_aligned a = true.
Proof.
 rewrite baseline_bitmap_address; intros [i [Hi ->]].
 change (aligned 3 (n2w (initDataRam+24+8*i) : word 64) = true).
 replace (initDataRam+24+8*i) with (initDataRam+8*(i+3)) by lia.
 apply copy_address_alignment; auto.
Qed.
Lemma baseline_bitmap_align a : baselineBitmapDomain a -> byte_align a = a.
Proof. intro Ha; apply (proj1 (byte_align_aligned a)); apply baseline_bitmap_aligned; exact Ha. Qed.
Lemma baseline_bitmap_lane_range a j : baselineBitmapDomain a -> j < 8 ->
 initDataRam+24 <= w2n (a+n2w j)%w /\ w2n (a+n2w j)%w < initDataEnd.
Proof.
 rewrite baseline_bitmap_address; intros [i [Hi ->]] Hj.
 pose proof (proj1 (proj2 original_literal_sizes)) as Hsize.
 change (LENGTH bitmaps = 4614) in Hsize; rewrite Hsize in Hi.
 replace (initDataRam+24+8*i) with (initDataRam+8*(i+3)) by lia.
 rewrite copy_address_value by (auto; lia).
 unfold initDataEnd,bitmapWordCount; lia.
Qed.
Lemma baseline_bitmap_lane_domain a j : baselineBitmapDomain a -> j < 8 ->
 bootstrapDomain (a+n2w j)%w.
Proof.
 intros Ha Hj; apply copy_range_domain; right.
 pose proof (baseline_bitmap_lane_range a j Ha Hj); lia.
Qed.
Lemma baseline_bitmap_byte_domain a : baselineBitmapDomain (byte_align a) -> bootstrapDomain a.
Proof.
 intro Ha; pose proof (baseline_bitmap_lane_domain (byte_align a) (w2n a mod 8) Ha
  (N.mod_lt (w2n a) 8 ltac:(discriminate))) as Hd.
 rewrite byte_align_64_eq in Hd by reflexivity; exact Hd.
Qed.
Lemma baseline_bitmap_lane_disjoint a j : baselineBitmapDomain a -> j < 8 ->
 ~ (sourceBase <= w2n (a+n2w j)%w /\ w2n (a+n2w j)%w < sourceBase+40) /\
 ~ (heapStart <= w2n (a+n2w j)%w /\ w2n (a+n2w j)%w < heapEnd) /\
 ~ (stackStart <= w2n (a+n2w j)%w /\ w2n (a+n2w j)%w < ramEnd) /\
 ~ submissionSharedDomain (a+n2w j)%w.
Proof.
 intros Ha Hj; pose proof (baseline_bitmap_lane_range a j Ha Hj) as Hr.
 unfold submissionSharedDomain; cbv [initDataRam initDataEnd bitmapWordCount
  sourceBase heapStart scratchEnd heapEnd stackStart ramEnd ramStart ramSize
  stackSize globalsWords inputStart inputEnd inputSize outputStart outputEnd outputSize] in *.
 repeat split; intros H; lia.
Qed.

(** [installed] uses a byte-closed domain, intersected with aligned addresses
    for the separation assertion. This gives exactly the graph proved above. *)
Definition baselineBitmapByteDomain (a : word 64) : Prop :=
 baselineBitmapDomain (byte_align a).
Lemma baseline_bitmap_domain_closed a :
 baselineBitmapByteDomain (byte_align a) -> baselineBitmapByteDomain a.
Proof. unfold baselineBitmapByteDomain; rewrite packed_byte_align_twice; auto. Qed.
Lemma baseline_bitmap_domain_subset : baselineBitmapByteDomain SUBSET bootstrapDomain.
Proof. intros a Ha; apply baseline_bitmap_byte_domain; exact Ha. Qed.
Lemma baseline_bitmap_domain_intersection :
 (fun a : word 64 => byte_aligned a) INTER baselineBitmapByteDomain = baselineBitmapDomain.
Proof.
 apply set_ext; intros a; unfold pred_set.INTER,pred_set.IN,baselineBitmapByteDomain; split.
 - intros [Haligned Ha]; rewrite (proj1 (byte_align_aligned a) Haligned) in Ha; exact Ha.
 - intro Ha; split; [apply baseline_bitmap_aligned; exact Ha|].
   rewrite baseline_bitmap_align by exact Ha; exact Ha.
Qed.
Lemma baseline_bitmap_byte_range a : baselineBitmapByteDomain a ->
 initDataRam+24 <= w2n a /\ w2n a < initDataEnd.
Proof.
 intro Ha; pose proof (baseline_bitmap_lane_range (byte_align a) (w2n a mod 8) Ha
  (N.mod_lt (w2n a) 8 ltac:(discriminate))) as Hr.
 rewrite byte_align_64_eq in Hr by reflexivity; exact Hr.
Qed.
Lemma baseline_bitmap_byte_disjoint a : baselineBitmapByteDomain a ->
 ~ (sourceBase <= w2n a /\ w2n a < sourceBase+40) /\
 ~ (heapStart <= w2n a /\ w2n a < heapEnd) /\
 ~ (stackStart <= w2n a /\ w2n a < ramEnd) /\ ~ submissionSharedDomain a.
Proof.
 intro Ha; pose proof (baseline_bitmap_lane_disjoint (byte_align a) (w2n a mod 8) Ha
  (N.mod_lt (w2n a) 8 ltac:(discriminate))) as Hd.
 rewrite byte_align_64_eq in Hd by reflexivity; exact Hd.
Qed.
Lemma baseline_bitmap_end_address :
 (n2w (initDataRam+24)+bytes_in_word*n2w (LENGTH bitmaps) : word 64)%w = n2w initDataEnd.
Proof.
 change (bytes_in_word : word 64) with (n2w 8 : word 64).
 rewrite word_mul_n2w,word_add_n2w.
 pose proof (proj1 (proj2 original_literal_sizes)) as Hsize.
 change (LENGTH bitmaps = 4614) in Hsize; rewrite Hsize; reflexivity.
Qed.
Theorem baseline_bitmap_installed_separation :
 STAR (word_list (n2w (initDataRam+24)) (MAP (@Word 64) bitmaps))
  (word_list_exists (n2w (initDataRam+24)+bytes_in_word*n2w (LENGTH bitmaps))%w 0)
  (fun2set (packedWordMemory installedMemory,
   (fun a : word 64 => byte_aligned a) INTER baselineBitmapByteDomain)).
Proof.
 rewrite baseline_bitmap_end_address,baseline_bitmap_domain_intersection.
 exact baseline_bitmap_separation.
Qed.

Lemma baseline_bitmap_heap_stack_disjoint :
 DISJOINT (fun a : word 64 => sourceBase <= w2n a /\ w2n a < ramEnd)
  baselineBitmapByteDomain.
Proof.
 unfold DISJOINT; apply set_ext; intro a; unfold pred_set.INTER,pred_set.IN,pred_set.EMPTY.
 split; [|intros []]. intros [[Hlo Hhi] Ha].
 pose proof (baseline_bitmap_byte_range a Ha) as Hr.
 cbv [initDataEnd initDataRam bitmapWordCount sourceBase] in *; lia.
Qed.
Lemma baseline_bitmap_code_disjoint a : baselineBitmapByteDomain a ->
 ~ (initialPc <= w2n a /\ w2n a < initialPc+codeSizeLimit).
Proof.
 intro Ha; pose proof (baseline_bitmap_byte_range a Ha) as Hr.
 cbv [initialPc codeSizeLimit initDataRam] in *; lia.
Qed.
