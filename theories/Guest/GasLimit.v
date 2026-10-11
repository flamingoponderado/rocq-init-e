(** The challenge reader from Guest/GasLimit.lean, not a validator.
    Missing bytes are zero; SSZ offsets are followed without validation. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
Open Scope N_scope.
From InitE.Guest Require Export Basic.
Definition byte (input : InputBlob) (i : N) : N :=
  w2n (nthN i input (n2w 0)).
Definition le32 (input : InputBlob) (i : N) : N :=
 byte input i + byte input (i+1)*256 + byte input (i+2)*65536 + byte input (i+3)*16777216.
Definition le64 (input : InputBlob) (i : N) : N :=
 le32 input i + le32 input (i+4)*4294967296.
Definition declaredGasLimit (input : InputBlob) : N :=
 let requestStart := 2 + le32 input 2 in
 let payloadStart := requestStart + le32 input requestStart in
 le64 input (payloadStart+412).
Example empty_gas_limit : declaredGasLimit [] = 0.
Proof. vm_compute; reflexivity. Qed.
Example maximum_offset_short_input :
 declaredGasLimit [n2w 0;n2w 0;n2w 255;n2w 255;n2w 255;n2w 255] = 0.
Proof. vm_compute; reflexivity. Qed.
