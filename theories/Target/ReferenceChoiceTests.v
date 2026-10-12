(** Regression for the original separate opaque failed-THE interface. *)
From Galette Require Import Base.
From InitE.Target Require Import ReducedTypes ReferenceChoices.
Fail Transparent ReferenceChoices.theNone.
Fail Definition none_is_arb :
 (ReferenceChoices.theNone : ReducedTypes.riscv_state) = (ARB : ReducedTypes.riscv_state) := eq_refl.
Example successful_the x : referenceThe (Some x : option ReducedTypes.riscv_state) = x.
Proof. reflexivity. Qed.
