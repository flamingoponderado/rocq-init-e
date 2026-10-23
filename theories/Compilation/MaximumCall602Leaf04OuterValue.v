From Galette Require Import Base.
From InitE.Compilation Require Import MaximumCall602Via606Context MaximumCall602Leaf04Context MaximumCall602Leaf04Split MaximumCall602Leaf04Value.

Lemma depth_cached :
  MaximumCall602Via606Context.depth MaximumCall602Leaf04Context.outer = MaximumCall602Leaf04Value.depth_value.
Proof.
  rewrite MaximumCall602Leaf04Split.outer_depth_split.
  unfold MaximumCall602Leaf04Value.depth_value.
  now rewrite MaximumCall602Leaf04Value.values_eq.
Qed.

Definition value := Eval vm_compute in MaximumCall602Leaf04Value.depth_value.
Lemma value_eq : MaximumCall602Via606Context.depth MaximumCall602Leaf04Context.outer = value.
Proof.
  rewrite depth_cached.
  vm_cast_no_check (eq_refl value).
Qed.
