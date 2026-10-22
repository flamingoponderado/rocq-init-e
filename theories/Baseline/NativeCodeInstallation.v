(** Actual original native bytes remain loaded at the reached native entry. *)
From Galette Require Import Base.
From Stdlib Require Import NArith Lia Bool.
From Galette.HOL.src.n_bit Require Import words byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.encoders.asm Require Import asmSem asmProps.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From InitE.Guest Require Import Basic.
From InitE.Target Require Import ReducedTypes Configuration.
From InitE.InitE Require Import Parameters SubmissionModel BaselineArtifactLayout.
From InitE.Baseline Require Import Artifacts ArtifactFacts BitmapImageFacts BootstrapMemory BootstrapCopyBounds BootstrapCodeFacts BootstrapCopyChecked BootstrapInstalledMemory PackedWordMemory Submission BootstrapInitialRelation.
Open Scope N_scope.
Local Opaque bootPrefix nativeCode suffix bitmaps bootstrapEndpoint.
Lemma native_literal_length : LENGTH nativeCode = 979140.
Proof. exact (proj1 original_literal_sizes). Qed.
Lemma native_address_value offset : offset <= 982928 ->
 w2n (n2w nativePc+n2w offset : word 64)%w = nativePc+offset.
Proof.
 intro Ho; rewrite word_add_n2w,w2n_n2w; change (dimword 64) with (2^64).
 apply N.mod_small; unfold nativePc; lia.
Qed.
Theorem original_native_rom_byte offset : offset < LENGTH nativeCode ->
 romMemory (n2w nativePc+n2w offset)%w = nthN offset nativeCode (n2w 0).
Proof.
 intro Ho; pose proof Ho as Hbound; rewrite native_literal_length in Hbound.
 unfold romMemory; rewrite native_address_value by lia.
 pose proof (proj2 (proj2 (proj2 original_literal_sizes))) as Hlength.
 assert (Hg : (initialPc <=? nativePc+offset) && (nativePc+offset <? initialPc+LENGTH code) = true).
 { rewrite Hlength; apply andb_true_iff; split; [apply N.leb_le|apply N.ltb_lt];
   cbv [initialPc nativePc fullRomByteCount]; lia. }
 rewrite Hg; unfold code.
 rewrite nthN_append_right by (rewrite (proj1 (proj2 (proj2 original_literal_sizes))); cbv [nativePc initialPc]; lia).
 rewrite (proj1 (proj2 (proj2 original_literal_sizes))).
 replace (nativePc+offset-initialPc-(nativePc-2147483648)) with offset by (unfold initialPc,nativePc; lia).
 apply nthN_append_left; exact Ho.
Qed.
Theorem installed_native_byte offset : offset < LENGTH nativeCode ->
 installedMemory (n2w nativePc+n2w offset)%w = nthN offset nativeCode (n2w 0).
Proof.
 intro Ho; pose proof Ho as Hbound; rewrite native_literal_length in Hbound.
 unfold installedMemory; rewrite native_address_value by lia.
 assert (Hs : (sourceBase <=? nativePc+offset) = false) by (apply N.leb_gt; cbv [sourceBase nativePc]; lia).
 assert (Hr : (initDataRam <=? nativePc+offset) = false) by (apply N.leb_gt; cbv [initDataRam nativePc]; lia).
 assert (Hb : (initDataRam+24 <=? nativePc+offset) = false) by (apply N.leb_gt; cbv [initDataRam nativePc]; lia).
 rewrite Hs,Hr,Hb; cbn; apply original_native_rom_byte; exact Ho.
Qed.
Theorem native_code_buffer_domain a : nativePc <= w2n a -> w2n a < codeBufferLimit -> bootstrapDomain a.
Proof.
 intros Hlo Hhi; unfold bootstrapDomain; split.
 - unfold submissionMemoryDomain,submissionSharedDomain; split.
   + left; cbv [nativePc codeBufferLimit initialPc codeSizeLimit] in *; split; lia.
   + cbv [nativePc codeBufferLimit inputStart inputEnd inputSize outputStart outputEnd outputSize] in *.
     intros [[H1 H2]|[H1 H2]]; lia.
 - intros i Hi E.
   assert (Hin : In i (COUNT_LIST 4)) by (apply bootstrap_count_in; exact Hi).
   assert (Hslot : w2n ((n2w nativePc-n2w (16*(i+1)))%w : word 64) < nativePc).
   { vm_compute in Hin; repeat destruct Hin as [Hin|Hin]; try contradiction; subst i; vm_compute; congruence. }
   rewrite <- E in Hslot; lia.
Qed.
Theorem native_byte_domain offset : offset < LENGTH nativeCode ->
 bootstrapDomain (n2w nativePc+n2w offset)%w.
Proof.
 intro Ho; rewrite native_literal_length in Ho; apply native_code_buffer_domain;
 rewrite native_address_value by lia; cbv [nativePc codeBufferLimit]; lia.
Qed.
Theorem endpoint_native_byte offset : offset < LENGTH nativeCode ->
 mem bootstrapEndpoint (n2w nativePc+n2w offset)%w = nthN offset nativeCode (n2w 0).
Proof. intro Ho; rewrite bootstrap_endpoint_memory; apply installed_native_byte; exact Ho. Qed.
Theorem endpoint_native_code_loaded ms : target_state_rel riscvTarget bootstrapEndpoint ms ->
 code_loaded nativeCode (machineConfig baselineSubmission) ms.
Proof.
 intros [_ [Hpc [Hmem _]]]; rewrite bootstrap_endpoint_pc in Hpc.
 unfold code_loaded; change (read_bytearray (get_pc riscvTarget ms) (LENGTH nativeCode)
  (fun ad => if classical_dec (bootstrapDomain ad) then Some (get_byte riscvTarget ms ad) else None) = Some nativeCode).
 rewrite Hpc; apply read_bytearray_literal; intros j Hj.
 pose proof (native_byte_domain j Hj) as Hd.
 destruct (classical_dec (bootstrapDomain (n2w nativePc+n2w j)%w)) as [Hdomain|Hdomain]; [|contradiction].
 rewrite Hmem.
 - exact (f_equal (@Some (word 8)) (endpoint_native_byte j Hj)).
 - rewrite (proj1 bootstrap_endpoint_controls); exact Hd.
Qed.
