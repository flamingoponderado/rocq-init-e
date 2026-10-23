From Galette Require Import Base.
From InitE.Compilation Require Import MaximumCall621Via595Context
  MaximumCall621Leaf148Context MaximumCall621Leaf148Split
  MaximumCall621Leaf148Value.

Lemma depth_cached :
  MaximumCall621Via595Context.depth MaximumCall621Leaf148Context.outer =
  MaximumCall621Leaf148Value.depth_value.
Proof.
  rewrite MaximumCall621Leaf148Split.outer_depth_split.
  unfold MaximumCall621Leaf148Value.depth_value.
  now rewrite MaximumCall621Leaf148Value.values_eq.
Qed.

Definition value := Eval vm_compute in MaximumCall621Leaf148Value.depth_value.
Lemma value_eq :
  MaximumCall621Via595Context.depth MaximumCall621Leaf148Context.outer = value.
Proof.
  rewrite depth_cached.
  vm_cast_no_check (eq_refl value).
Qed.
