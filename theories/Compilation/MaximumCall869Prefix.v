From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumCall869Context MaximumCall869Pieces.

Definition values := Eval vm_compute in List.map MaximumCall869Context.depth MaximumCall869Pieces.prefix.
Lemma values_eq : List.map MaximumCall869Context.depth MaximumCall869Pieces.prefix = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
