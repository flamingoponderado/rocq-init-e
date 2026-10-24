From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumCall868Context MaximumCall868Pieces.

Definition values := Eval vm_compute in List.map MaximumCall868Context.depth MaximumCall868Pieces.prefix.
Lemma values_eq : List.map MaximumCall868Context.depth MaximumCall868Pieces.prefix = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
