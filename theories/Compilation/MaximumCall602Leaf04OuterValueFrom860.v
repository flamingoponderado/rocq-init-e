From Galette Require Import Base.
From InitE.Compilation Require Import MaximumCall602Via606ContextFrom860 MaximumCall602Leaf04ContextFrom860 MaximumCall602Leaf04SplitFrom860 MaximumCall602Leaf04ValueFrom860.

Lemma depth_cached :
  MaximumCall602Via606ContextFrom860.depth MaximumCall602Leaf04ContextFrom860.outer = MaximumCall602Leaf04ValueFrom860.depth_value.
Proof.
  rewrite MaximumCall602Leaf04SplitFrom860.outer_depth_split.
  unfold MaximumCall602Leaf04ValueFrom860.depth_value.
  now rewrite MaximumCall602Leaf04ValueFrom860.values_eq.
Qed.

Definition value := Eval vm_compute in MaximumCall602Leaf04ValueFrom860.depth_value.
Lemma value_eq : MaximumCall602Via606ContextFrom860.depth MaximumCall602Leaf04ContextFrom860.outer = value.
Proof.
  rewrite depth_cached.
  vm_cast_no_check (eq_refl value).
Qed.
