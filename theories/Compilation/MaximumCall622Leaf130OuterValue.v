From Galette Require Import Base.
From InitE.Compilation Require Import MaximumCall622Via595Context MaximumCall622Leaf130Context MaximumCall622Leaf130Split MaximumCall622Leaf130Value.

Lemma depth_cached :
  MaximumCall622Via595Context.depth MaximumCall622Leaf130Context.outer = MaximumCall622Leaf130Value.depth_value.
Proof.
  rewrite MaximumCall622Leaf130Split.outer_depth_split.
  unfold MaximumCall622Leaf130Value.depth_value.
  now rewrite MaximumCall622Leaf130Value.values_eq.
Qed.

Definition value := Eval vm_compute in MaximumCall622Leaf130Value.depth_value.
Lemma value_eq : MaximumCall622Via595Context.depth MaximumCall622Leaf130Context.outer = value.
Proof.
  rewrite depth_cached.
  vm_cast_no_check (eq_refl value).
Qed.
