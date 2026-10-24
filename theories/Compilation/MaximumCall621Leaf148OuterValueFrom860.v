From Galette Require Import Base.
From InitE.Compilation Require Import MaximumCall621Via595ContextFrom860
  MaximumCall621Leaf148ContextFrom860 MaximumCall621Leaf148SplitFrom860
  MaximumCall621Leaf148ValueFrom860.

Lemma depth_cached :
  MaximumCall621Via595ContextFrom860.depth MaximumCall621Leaf148ContextFrom860.outer =
  MaximumCall621Leaf148ValueFrom860.depth_value.
Proof.
  rewrite MaximumCall621Leaf148SplitFrom860.outer_depth_split.
  unfold MaximumCall621Leaf148ValueFrom860.depth_value.
  now rewrite MaximumCall621Leaf148ValueFrom860.values_eq.
Qed.

Definition value := Eval vm_compute in MaximumCall621Leaf148ValueFrom860.depth_value.
Lemma value_eq :
  MaximumCall621Via595ContextFrom860.depth MaximumCall621Leaf148ContextFrom860.outer = value.
Proof.
  rewrite depth_cached.
  vm_cast_no_check (eq_refl value).
Qed.
