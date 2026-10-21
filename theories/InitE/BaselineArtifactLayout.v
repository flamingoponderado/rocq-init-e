(** Concrete original baseline locations. Counts are proposal literals until
    the separate compilation equality is proved; no challenge premise changes. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.Guest Require Import Bookkeeping.
From InitE.InitE Require Import Parameters.
Open Scope N_scope.
Definition nativePc : N := 2147487856.
Definition nativeByteCount : N := 979140.
Definition bitmapWordCount : N := 4603.
Definition initDataRom : N := 2148474880.
Definition initDataRam : N := 2684485632.
Definition initDataEnd : N := initDataRam + 24 + 8 * bitmapWordCount.
Definition codeBufferEnd : N := nativePc + nativeByteCount.
Definition codeBufferLimit : N := 2148470784.
Definition fullRomByteCount : N := 1028080.
Theorem original_startup_layout :
 Bookkeeping.startupHeaders =
 [n2w (initDataRam+24); n2w initDataEnd; n2w initDataEnd;
  n2w codeBufferEnd; n2w codeBufferLimit].
Proof. vm_compute; reflexivity. Qed.
Theorem original_artifact_regions :
 nativePc-initialPc = 4208 /\
 codeBufferEnd <= codeBufferLimit /\ codeBufferLimit <= initDataRom /\
 initDataRom-initialPc + 24 + bitmapWordCount*8 <= fullRomByteCount /\
 0 < fullRomByteCount /\ fullRomByteCount <= codeSizeLimit /\
 ramStart <= initDataRam /\ initDataEnd <= outputStart /\
 initDataEnd mod 8 = 0 /\ nativePc mod 4 = 0 /\
 538*8 < stackSize.
Proof. repeat split; vm_compute; congruence. Qed.
