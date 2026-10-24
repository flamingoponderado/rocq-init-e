From Galette Require Import Base.
From InitE.Compilation Require Import MaximumCall625Via860Context MaximumCall625Leaf13ContextFrom860 MaximumCall625Leaf13SplitFrom860 MaximumCall625Leaf13ValueFrom860.

Lemma depth_cached :
  MaximumCall625Via860Context.depth MaximumCall625Leaf13ContextFrom860.outer = MaximumCall625Leaf13ValueFrom860.depth_value.
Proof.
  rewrite MaximumCall625Leaf13SplitFrom860.outer_depth_split.
  unfold MaximumCall625Leaf13ValueFrom860.depth_value.
  now rewrite MaximumCall625Leaf13ValueFrom860.values_eq.
Qed.

Definition value := Eval vm_compute in MaximumCall625Leaf13ValueFrom860.depth_value.
Lemma value_eq : MaximumCall625Via860Context.depth MaximumCall625Leaf13ContextFrom860.outer = value.
Proof.
  rewrite depth_cached.
  vm_cast_no_check (eq_refl value).
Qed.
