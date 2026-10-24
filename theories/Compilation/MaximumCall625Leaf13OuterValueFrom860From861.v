From Galette Require Import Base.
From InitE.Compilation Require Import MaximumCall625Via860ContextFrom861 MaximumCall625Leaf13ContextFrom860From861 MaximumCall625Leaf13SplitFrom860From861 MaximumCall625Leaf13ValueFrom860From861.

Lemma depth_cached :
  MaximumCall625Via860ContextFrom861.depth MaximumCall625Leaf13ContextFrom860From861.outer = MaximumCall625Leaf13ValueFrom860From861.depth_value.
Proof.
  rewrite MaximumCall625Leaf13SplitFrom860From861.outer_depth_split.
  unfold MaximumCall625Leaf13ValueFrom860From861.depth_value.
  now rewrite MaximumCall625Leaf13ValueFrom860From861.values_eq.
Qed.

Definition value := Eval vm_compute in MaximumCall625Leaf13ValueFrom860From861.depth_value.
Lemma value_eq : MaximumCall625Via860ContextFrom861.depth MaximumCall625Leaf13ContextFrom860From861.outer = value.
Proof.
  rewrite depth_cached.
  vm_cast_no_check (eq_refl value).
Qed.
