(** Boundary checks against original RV64IM instruction restrictions. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.examples.l3_machine_code.riscv.model Require Import riscv.
From InitE.Target Require Import Decode.
Open Scope N_scope.
Example nop_decodes : Decode.Decode (n2w 19) = ArithI (ADDI (n2w 0,n2w 0,n2w 0)).
Proof. vm_compute; repeat f_equal; try reflexivity; apply proof_irrelevance. Qed.
Example addiw_supported : Decode.Decode (n2w 27) = ArithI (ADDIW (n2w 0,n2w 0,n2w 0)).
Proof. vm_compute; repeat f_equal; try reflexivity; apply proof_irrelevance. Qed.
Example addw_rejected : Decode.Decode (n2w 59) = UnknownInstruction.
Proof. vm_compute; repeat f_equal; try reflexivity; apply proof_irrelevance. Qed.
Example atomic_rejected : Decode.Decode (n2w 8239) = UnknownInstruction.
Proof. vm_compute; repeat f_equal; try reflexivity; apply proof_irrelevance. Qed.
Example fp_rejected : Decode.Decode (n2w 83) = UnknownInstruction.
Proof. vm_compute; repeat f_equal; try reflexivity; apply proof_irrelevance. Qed.
Example csr_rejected : Decode.Decode (n2w 4211) = UnknownInstruction.
Proof. vm_compute; repeat f_equal; try reflexivity; apply proof_irrelevance. Qed.
Example compressed_rejected : Decode.DecodeRVC (n2w 1) = UnknownInstruction.
Proof. reflexivity. Qed.
