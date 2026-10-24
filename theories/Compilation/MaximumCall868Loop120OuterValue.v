From Galette Require Import Base.
From InitE.Compilation Require Import MaximumCall868Context MaximumCall868Loop120Context MaximumCall868Loop120Split MaximumCall868Loop120Value.

Lemma depth_cached :
  MaximumCall868Context.depth MaximumCall868Loop120Context.outer = MaximumCall868Loop120Value.depth_value.
Proof.
  rewrite MaximumCall868Loop120Split.outer_depth_split.
  unfold MaximumCall868Loop120Value.depth_value.
  now rewrite MaximumCall868Loop120Value.values_eq.
Qed.

Definition value := Eval vm_compute in MaximumCall868Loop120Value.depth_value.
Lemma value_eq : MaximumCall868Context.depth MaximumCall868Loop120Context.outer = value.
Proof.
  rewrite depth_cached.
  vm_cast_no_check (eq_refl value).
Qed.
