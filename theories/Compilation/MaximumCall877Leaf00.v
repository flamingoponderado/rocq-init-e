From Galette Require Import Base.
From InitE.Compilation Require Import MaximumCall877Context.

Definition values := Eval vm_compute in
  List.map MaximumCall877Context.depth (MaximumCall877Context.leaf_chunk 0).
Lemma values_eq :
  List.map MaximumCall877Context.depth (MaximumCall877Context.leaf_chunk 0) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
