(** Kernel binding of the original ROM bitmap bytes to the original word literals. *)
From Galette Require Import Base.
From Stdlib Require Import List NArith Lia.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list.
From InitE.Guest Require Import Basic.
From InitE.InitE Require Import BaselineArtifactLayout.
From InitE.Baseline Require Import Artifacts ArtifactFacts BootstrapMemory.
Open Scope N_scope.
Definition bitmapWordBytes (value : word 64) : list (word 8) :=
 [wordByte value 0;wordByte value 1;wordByte value 2;wordByte value 3;
  wordByte value 4;wordByte value 5;wordByte value 6;wordByte value 7].
Definition bitmapBytes : list (word 8) := concat (MAP bitmapWordBytes bitmaps).
Lemma drop_append_skip {A} n (left right : list A) : LENGTH left <= n ->
 DROP n (left++right) = DROP (n-LENGTH left) right.
Proof.
 intro H; rewrite !DROP_skipn,skipn_app.
 assert (Hlength : (length left <= N.to_nat n)%nat).
 { rewrite LENGTH_length in H; lia. }
 rewrite skipn_all2 by exact Hlength; cbn [app].
 rewrite N2Nat.inj_sub,LENGTH_length,Nat2N.id; reflexivity.
Qed.
Lemma word_list_numeric_ext {width} (xs ys : list (word width)) :
 MAP w2n xs = MAP w2n ys -> xs = ys.
Proof.
 revert ys; induction xs as [|x xs IH]; intros ys H; destruct ys as [|y ys]; cbn [MAP] in H.
 - reflexivity.
 - discriminate.
 - discriminate.
 - inversion H as [[Hhead Htail]].
   f_equal; [apply w2n_11; exact Hhead|apply IH; exact Htail].
Qed.
Theorem bitmap_suffix_bytes : DROP 4740 suffix = bitmapBytes.
Proof. apply word_list_numeric_ext; vm_compute; reflexivity. Qed.
Local Opaque bootPrefix nativeCode suffix bitmaps bitmapBytes.
Theorem bitmap_image_bytes : DROP (initDataRom-2147483648+24) code = bitmapBytes.
Proof.
 destruct original_literal_sizes as [Hnative [Hbitmaps [Hprefix Hcode]]].
 change (LENGTH nativeCode = 904196) in Hnative.
 change (LENGTH bootPrefix = 4496) in Hprefix.
 unfold code; change (DROP 913432 (bootPrefix++nativeCode++suffix) = bitmapBytes).
 rewrite drop_append_skip by (rewrite Hprefix; lia).
 rewrite Hprefix; change (DROP 908936 (nativeCode++suffix) = bitmapBytes).
 rewrite drop_append_skip by (rewrite Hnative; lia).
 rewrite Hnative; exact bitmap_suffix_bytes.
Qed.

Lemma bitmap_word_bytes_size value : LENGTH (bitmapWordBytes value) = 8.
Proof. reflexivity. Qed.
Lemma bitmap_word_byte_index value j : j < 8 ->
 nthN j (bitmapWordBytes value) (n2w 0) = wordByte value j.
Proof.
 intro Hj; assert (E : j=0 \/ j=1 \/ j=2 \/ j=3 \/ j=4 \/ j=5 \/ j=6 \/ j=7) by lia.
 repeat destruct E as [E|E]; subst j; reflexivity.
Qed.
Lemma nthN_append_left {A} i (left right : list A) default : i < LENGTH left ->
 nthN i (left++right) default = nthN i left default.
Proof.
 intro H; rewrite !nthN_eq_nth; apply app_nth1; rewrite LENGTH_length in H; lia.
Qed.
Lemma nthN_append_right {A} i (left right : list A) default : LENGTH left <= i ->
 nthN i (left++right) default = nthN (i-LENGTH left) right default.
Proof.
 intro H; rewrite !nthN_eq_nth; rewrite app_nth2 by (rewrite LENGTH_length in H; lia).
 rewrite N2Nat.inj_sub,LENGTH_length,Nat2N.id; reflexivity.
Qed.
Theorem bitmap_list_byte_index values i j : i < LENGTH values -> j < 8 ->
 nthN (8*i+j) (concat (MAP bitmapWordBytes values)) (n2w 0) =
 wordByte (nthN i values (n2w 0)) j.
Proof.
 revert i; induction values as [|value rest IH]; intros i Hi Hj.
 - cbn [LENGTH] in Hi; lia.
 - cbn [MAP concat]; destruct (N.eq_dec i 0) as [E|Hpos].
   + subst i; change (nthN j (bitmapWordBytes value++concat (MAP bitmapWordBytes rest)) (n2w 0) = wordByte value j).
     rewrite nthN_append_left by (rewrite bitmap_word_bytes_size; exact Hj).
     apply bitmap_word_byte_index; exact Hj.
   + rewrite nthN_append_right by (rewrite bitmap_word_bytes_size; lia).
     rewrite bitmap_word_bytes_size.
     replace (8*i+j-8) with (8*(i-1)+j) by lia.
     cbn [nthN]; assert (Ei : (i =? 0) = false) by (apply N.eqb_neq; exact Hpos).
     rewrite Ei; apply IH; [cbn [LENGTH] in Hi; lia|exact Hj].
Qed.
