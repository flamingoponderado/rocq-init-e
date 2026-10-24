From Galette Require Import Base.
From InitE.Compilation Require Import MaximumCall621Via595ContextFrom608From860From861
  MaximumCall621Leaf148ContextFrom608From860From861 MaximumCall621Leaf148SplitFrom608From860From861
  MaximumCall621Leaf148ValueFrom608From860From861.

Lemma depth_cached :
  MaximumCall621Via595ContextFrom608From860From861.depth MaximumCall621Leaf148ContextFrom608From860From861.outer =
  MaximumCall621Leaf148ValueFrom608From860From861.depth_value.
Proof.
  rewrite MaximumCall621Leaf148SplitFrom608From860From861.outer_depth_split.
  unfold MaximumCall621Leaf148ValueFrom608From860From861.depth_value.
  now rewrite MaximumCall621Leaf148ValueFrom608From860From861.values_eq.
Qed.

Definition value := Eval vm_compute in MaximumCall621Leaf148ValueFrom608From860From861.depth_value.
Lemma value_eq :
  MaximumCall621Via595ContextFrom608From860From861.depth MaximumCall621Leaf148ContextFrom608From860From861.outer = value.
Proof.
  rewrite depth_cached.
  vm_cast_no_check (eq_refl value).
Qed.
