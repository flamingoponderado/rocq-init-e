From Galette Require Import Base.
From InitE.Compilation Require Import MaximumCall602Via606ContextFrom608 MaximumCall602Leaf04ContextFrom608 MaximumCall602Leaf04SplitFrom608 MaximumCall602Leaf04ValueFrom608.

Lemma depth_cached :
  MaximumCall602Via606ContextFrom608.depth MaximumCall602Leaf04ContextFrom608.outer = MaximumCall602Leaf04ValueFrom608.depth_value.
Proof.
  rewrite MaximumCall602Leaf04SplitFrom608.outer_depth_split.
  unfold MaximumCall602Leaf04ValueFrom608.depth_value.
  now rewrite MaximumCall602Leaf04ValueFrom608.values_eq.
Qed.

Definition value := Eval vm_compute in MaximumCall602Leaf04ValueFrom608.depth_value.
Lemma value_eq : MaximumCall602Via606ContextFrom608.depth MaximumCall602Leaf04ContextFrom608.outer = value.
Proof.
  rewrite depth_cached.
  vm_cast_no_check (eq_refl value).
Qed.
