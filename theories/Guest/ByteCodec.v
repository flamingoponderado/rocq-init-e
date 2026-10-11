(** Guest/AccelFfi.lean byte codecs; binary words are Galette words. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list rich_list.
Open Scope N_scope.
Definition leBytes (w : word 64) : list word8 :=
 MAP (fun i => n2w ((w2n w / 256^i) mod 256)) (COUNT_LIST 8).
Definition wordOfLeBytes (bytes : list word8) : word 64 :=
 n2w (fold_right (fun b acc => acc*256+w2n b) 0 bytes).
Fixpoint wordsOfLeBytes (bytes : list word8) : list (word 64) :=
 match bytes with
 | b0::b1::b2::b3::b4::b5::b6::b7::rest =>
   wordOfLeBytes [b0;b1;b2;b3;b4;b5;b6;b7] :: wordsOfLeBytes rest
 | _ => []
 end.
Definition leBytesOfWords (ws : list (word 64)) : list word8 :=
 flat_map leBytes ws.
Definition exactWords (configuration bytes : list word8) (n : N) : option (list (word 64)) :=
 if (LENGTH configuration =? 0) && (LENGTH bytes =? 8*n)
 then Some (wordsOfLeBytes bytes) else None.
Example partial_word_dropped : wordsOfLeBytes [n2w 1;n2w 2] = [].
Proof. reflexivity. Qed.
Example little_endian : w2n (wordOfLeBytes [n2w 1;n2w 2]) = 513.
Proof. vm_compute; reflexivity. Qed.
