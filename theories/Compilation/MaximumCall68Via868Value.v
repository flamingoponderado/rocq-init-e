From Galette Require Import Base.
From Galette.HOL.src.coretypes Require Import option.
From InitE.Compilation Require Import FastMaximum MaximumCall68Via868Context.

Definition values := Eval vm_compute in
  List.map MaximumCall68Via868Context.depth MaximumCall68Via868Context.leaves.
Lemma values_eq :
  List.map MaximumCall68Via868Context.depth MaximumCall68Via868Context.leaves = values.
Proof. vm_cast_no_check (eq_refl values). Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
