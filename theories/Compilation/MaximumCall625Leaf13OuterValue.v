From Galette Require Import Base.
From InitE.Compilation Require Import MaximumCall625Via863Context MaximumCall625Leaf13Context MaximumCall625Leaf13Split MaximumCall625Leaf13Value.

Lemma depth_cached :
  MaximumCall625Via863Context.depth MaximumCall625Leaf13Context.outer = MaximumCall625Leaf13Value.depth_value.
Proof.
  rewrite MaximumCall625Leaf13Split.outer_depth_split.
  unfold MaximumCall625Leaf13Value.depth_value.
  now rewrite MaximumCall625Leaf13Value.values_eq.
Qed.

Definition value := Eval vm_compute in MaximumCall625Leaf13Value.depth_value.
Lemma value_eq : MaximumCall625Via863Context.depth MaximumCall625Leaf13Context.outer = value.
Proof.
  rewrite depth_cached.
  vm_cast_no_check (eq_refl value).
Qed.
