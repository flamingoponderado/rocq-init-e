(** Actual installed ordinary words equal the unchanged original source memory. *)
From Galette Require Import Base.
From Stdlib Require Import List NArith Lia Bool.
From Galette.HOL.src.n_bit Require Import words byte alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.proofs Require stack_removeProof.
From Galette.cakeml.pancake.proofs Require pan_globalsProof crep_to_loopProof.
From Galette.cakeml.pancake.semantics Require panSem.
From InitE.Guest Require Import Basic Bookkeeping.
From InitE.InitE Require Import Parameters SourceSemantics BaselineArtifactLayout.
From InitE.Baseline Require Import BootstrapMemory BootstrapInstalledMemory BootstrapInitialRelation PackedWordMemory HeaderInstallation.
Open Scope N_scope.
Local Opaque romMemory.
Theorem installed_memory_zero_after_headers a : sourceBase+40 <= w2n a -> installedMemory a = n2w 0.
Proof.
 intro Hlo; unfold installedMemory.
 assert (Hs : (w2n a <? sourceBase+40) = false) by (apply N.ltb_ge; exact Hlo).
 assert (Hr : (w2n a <? initDataRam+24) = false) by (apply N.ltb_ge; cbv [sourceBase initDataRam] in *; lia).
 assert (Hb : (w2n a <? initDataEnd) = false) by (apply N.ltb_ge; cbv [sourceBase initDataEnd initDataRam bitmapWordCount] in *; lia).
 rewrite Hs,Hr,Hb,!andb_false_r; apply baseline_rom_ram_zero; cbv [sourceBase ramStart] in *; lia.
Qed.
Lemma source_index_bound i : i < (stackStart-sourceBase)/8-globalsWords -> sourceBase+8*i+8 < 2^64.
Proof. intro Hi; change (i < 3888119741) in Hi; unfold sourceBase; lia. Qed.
Lemma source_cell_value i : sourceBase+8*i < 2^64 ->
 w2n (n2w (sourceBase+8*i) : word 64) = sourceBase+8*i.
Proof. intro Hi; rewrite w2n_n2w; change (dimword 64) with (2^64); apply N.mod_small; exact Hi. Qed.
Lemma nthN_outside {A} i (values : list A) default : LENGTH values <= i -> nthN i values default = default.
Proof. intro Hi; rewrite nthN_eq_nth; apply nth_overflow; rewrite LENGTH_length in Hi; lia. Qed.
Theorem source_memory_cell i : sourceBase+8*i < 2^64 ->
 sourceMemory (n2w (sourceBase+8*i)) = panSem.Word (nthN i startupHeaders (n2w 0)).
Proof.
 intro Hi.
 assert (Hoffset : w2n ((n2w (sourceBase+8*i)-n2w sourceBase)%w : word 64) = 8*i).
 { rewrite <- word_add_n2w,WORD_ADD_SUB2,w2n_n2w.
   change (dimword 64) with (2^64); apply N.mod_small; lia. }
 unfold sourceMemory; rewrite Hoffset; cbn zeta.
 assert (Hmod : (8*i) mod 8 = 0) by (rewrite N.mul_comm; apply N.mod_mul; discriminate).
 assert (Hdiv : (8*i)/8 = i) by (rewrite N.mul_comm; apply N.div_mul; discriminate).
 rewrite Hmod,Hdiv; cbn [N.eqb andb].
 destruct (i <? LENGTH startupHeaders) eqn:Ei.
 - rewrite nthN_eq_nth; reflexivity.
 - apply N.ltb_ge in Ei; rewrite nthN_outside by exact Ei; reflexivity.
Qed.
Theorem installed_source_cell i : i < (stackStart-sourceBase)/8-globalsWords ->
 packedWordMemory installedMemory (n2w (sourceBase+8*i)) = wordLang.Word (nthN i startupHeaders (n2w 0)).
Proof.
 intro Hi; pose proof (source_index_bound i Hi) as Hbound.
 destruct (N.lt_ge_cases i 5) as [Hsmall|Hlarge].
 - apply installed_source_header_word; exact Hsmall.
 - assert (Hheaders : LENGTH startupHeaders <= i) by (change (5 <= i); exact Hlarge).
   rewrite nthN_outside by exact Hheaders.
   apply packedWordMemory_of_bytes.
   + change (aligned 3 (n2w (sourceBase+8*i) : word 64) = true).
     apply MOD_0_aligned; change ((sourceBase+8*i) mod 8 = 0).
     rewrite N.add_mod,N.mul_mod by discriminate; cbv [sourceBase]; rewrite N.mod_same by discriminate; cbn; reflexivity.
   + intros j Hj; rewrite installed_memory_zero_after_headers.
     * unfold byte.get_byte; reflexivity.
     * rewrite word_add_n2w,w2n_n2w; change (dimword 64) with (2^64).
       rewrite N.mod_small by lia; lia.
Qed.
Theorem installed_ordinary_word a : ordinaryDomain a ->
 packedWordMemory installedMemory a = crep_to_loopProof.wlab_wloc (sourceMemory a).
Proof.
 intro Ha; unfold ordinaryDomain in Ha; apply pan_globalsProof.in_addresses in Ha as [i [E Hi]].
 assert (Haddress : a = n2w (sourceBase+8*i)).
 { change (a = (n2w sourceBase+n2w i*n2w 8)%w) in E.
   rewrite word_mul_n2w,word_add_n2w in E; replace (i*8) with (8*i) in E by lia; exact E. }
 rewrite Haddress,source_memory_cell by (pose proof (source_index_bound i Hi); lia).
 change (packedWordMemory installedMemory (n2w (sourceBase+8*i)) = wordLang.Word (nthN i startupHeaders (n2w 0))).
 apply installed_source_cell; exact Hi.
Qed.
