(** Actual little-endian installed words for all original startup headers. *)
From Galette Require Import Base.
From Stdlib Require Import NArith Lia.
From Galette.HOL.src.n_bit Require Import words byte alignment.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.compiler.backend Require wordLang.
From InitE.Guest Require Import Basic Bookkeeping.
From InitE.InitE Require Import Parameters BaselineArtifactLayout.
From InitE.Baseline Require Import BootstrapMemory BootstrapTail BootstrapInstalledMemory PackedWordMemory BitmapInstallation.
Open Scope N_scope.
Lemma installed_header_alignment address value : In (address,value) tailHeaders ->
 byte_aligned (n2w address : word 64) = true.
Proof.
 unfold tailHeaders; intro Hin; repeat destruct Hin as [Hin|Hin]; try contradiction;
 inversion Hin; subst; vm_compute; reflexivity.
Qed.
Theorem installed_header_word address value : In (address,value) tailHeaders ->
 packedWordMemory installedMemory (n2w address) = wordLang.Word value.
Proof.
 intro Hi; apply packedWordMemory_of_bytes.
 - exact (installed_header_alignment address value Hi).
 - intros j Hj.
   rewrite <- bootstrap_endpoint_memory.
   rewrite (bootstrap_endpoint_headers address value j Hi Hj).
   rewrite <- installed_word_byte; apply bitmap_wordByte_get_byte; exact Hj.
Qed.
Theorem installed_source_header_word i : i < 5 ->
 packedWordMemory installedMemory (n2w (sourceBase+8*i)) =
 wordLang.Word (nthN i startupHeaders (n2w 0)).
Proof. intro Hi; apply installed_header_word; apply installed_source_header; exact Hi. Qed.
Theorem installed_init_header_word i : i < 3 ->
 packedWordMemory installedMemory (n2w (initDataRam+8*i)) =
 wordLang.Word (nthN i [n2w sourceBase;n2w stackStart;n2w ramEnd] (n2w 0)).
Proof. intro Hi; apply installed_header_word; apply installed_init_header; exact Hi. Qed.
