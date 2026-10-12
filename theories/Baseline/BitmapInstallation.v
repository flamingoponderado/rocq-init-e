(** The actual installed bitmap-region bytes recover the original word literals. *)
From Galette Require Import Base.
From Stdlib Require Import List NArith Lia Bool.
From Galette.HOL.src.n_bit Require Import words byte alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.compiler.backend Require wordLang.
From InitE.Guest Require Import Basic.
From InitE.InitE Require Import Parameters BaselineArtifactLayout.
From InitE.Baseline Require Import Artifacts ArtifactFacts BitmapImageFacts BootstrapMemory BootstrapCopyBounds BootstrapCopyInvariant BootstrapInstalledMemory PackedWordMemory.
Open Scope N_scope.
Local Opaque code bitmaps.
Lemma nthN_drop {A} i k (values : list A) default :
 nthN i (DROP k values) default = nthN (k+i) values default.
Proof.
 rewrite !nthN_eq_nth,DROP_skipn,nth_skipn,N2Nat.inj_add; reflexivity.
Qed.
Theorem original_rom_bitmap_byte i j : i < LENGTH bitmaps -> j < 8 ->
 romMemory (n2w (initDataRom+24+8*i+j)) = wordByte (nthN i bitmaps (n2w 0)) j.
Proof.
 intros Hi Hj; destruct original_literal_sizes as [Hnative [Hbitmaps [Hprefix Hcode]]].
 change (LENGTH bitmaps = 4614) in Hbitmaps; rewrite Hbitmaps in Hi.
 assert (Ha : w2n (n2w (initDataRom+24+8*i+j) : word 64) = initDataRom+24+8*i+j).
 { replace (initDataRom+24+8*i+j) with (initDataRom+(24+8*i+j)) by lia.
   apply copy_offset_value; [auto|lia]. }
 assert (Hlo : 2147483648 <= initDataRom+24+8*i+j) by (cbv [initDataRom]; lia).
 assert (Hhi : initDataRom+24+8*i+j < 2147483648+LENGTH code).
 { rewrite Hcode; cbv [initDataRom fullRomByteCount]; lia. }
 unfold romMemory; rewrite Ha.
 assert (Hguard : (initialPc <=? initDataRom+24+8*i+j) &&
  (initDataRom+24+8*i+j <? initialPc+LENGTH code) = true).
 { apply andb_true_iff; split; [apply N.leb_le; exact Hlo|apply N.ltb_lt; exact Hhi]. }
 rewrite Hguard.
 replace (initDataRom+24+8*i+j-initialPc) with ((initDataRom-2147483648+24)+(8*i+j)) by (unfold initialPc,initDataRom; lia).
 rewrite <- nthN_drop,bitmap_image_bytes.
 unfold bitmapBytes; apply bitmap_list_byte_index; [rewrite Hbitmaps; exact Hi|exact Hj].
Qed.
Theorem installed_bitmap_byte i j : i < LENGTH bitmaps -> j < 8 ->
 installedMemory (n2w (initDataRam+24+8*i)+n2w j)%w = wordByte (nthN i bitmaps (n2w 0)) j.
Proof.
 intros Hi Hj; pose proof (proj1 (proj2 original_literal_sizes)) as Hbitmaps.
 change (LENGTH bitmaps = 4614) in Hbitmaps; rewrite Hbitmaps in Hi.
 assert (Ha : w2n (n2w (initDataRam+24+8*i)+n2w j : word 64)%w = initDataRam+24+8*i+j).
 { replace (initDataRam+24+8*i) with (initDataRam+8*(i+3)) by lia.
   apply copy_address_value; [auto|lia|exact Hj]. }
 unfold installedMemory; rewrite Ha.
 assert (Hs : (sourceBase <=? initDataRam+24+8*i+j) && (initDataRam+24+8*i+j <? sourceBase+40) = false).
 { apply andb_false_iff; left; apply N.leb_gt; cbv [sourceBase initDataRam]; lia. }
 assert (Hd : (initDataRam <=? initDataRam+24+8*i+j) && (initDataRam+24+8*i+j <? initDataRam+24) = false).
 { apply andb_false_iff; right; apply N.ltb_ge; lia. }
 assert (Hb : (initDataRam+24 <=? initDataRam+24+8*i+j) && (initDataRam+24+8*i+j <? initDataEnd) = true).
 { apply andb_true_iff; split; [apply N.leb_le; lia|apply N.ltb_lt; cbv [initDataEnd bitmapWordCount]; lia]. }
 rewrite Hs,Hd,Hb.
 replace (initDataRom+(initDataRam+24+8*i+j)-initDataRam) with (initDataRom+24+8*i+j) by lia.
 apply original_rom_bitmap_byte; [rewrite Hbitmaps; exact Hi|exact Hj].
Qed.

Lemma bitmap_wordByte_get_byte value j : j < 8 ->
 wordByte value j = byte.get_byte (n2w j) value false.
Proof.
 intro Hj; rewrite installed_word_byte; unfold byte.get_byte.
 rewrite byte_index_n2w_le by exact Hj; reflexivity.
Qed.
Theorem installed_bitmap_word i : i < LENGTH bitmaps ->
 packedMemoryWord installedMemory (n2w (initDataRam+24+8*i)) = nthN i bitmaps (n2w 0).
Proof.
 intro Hi; apply packedMemoryWord_of_bytes.
 - change (aligned 3 (n2w (initDataRam+24+8*i) : word 64) = true).
   replace (initDataRam+24+8*i) with (initDataRam+8*(i+3)) by lia.
   apply copy_address_alignment; auto.
 - intros j Hj; rewrite installed_bitmap_byte by (exact Hi || exact Hj).
   apply bitmap_wordByte_get_byte; exact Hj.
Qed.
Theorem installed_bitmap_word_location i : i < LENGTH bitmaps ->
 packedWordMemory installedMemory (n2w (initDataRam+24+8*i)) = wordLang.Word (nthN i bitmaps (n2w 0)).
Proof.
 intro Hi; unfold packedWordMemory; rewrite installed_bitmap_word by exact Hi; reflexivity.
Qed.
