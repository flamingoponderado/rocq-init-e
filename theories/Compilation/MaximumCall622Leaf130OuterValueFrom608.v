From Galette Require Import Base.
From InitE.Compilation Require Import MaximumCall622Via595ContextFrom608 MaximumCall622Leaf130ContextFrom608 MaximumCall622Leaf130SplitFrom608 MaximumCall622Leaf130ValueFrom608.

Lemma depth_cached :
  MaximumCall622Via595ContextFrom608.depth MaximumCall622Leaf130ContextFrom608.outer = MaximumCall622Leaf130ValueFrom608.depth_value.
Proof.
  rewrite MaximumCall622Leaf130SplitFrom608.outer_depth_split.
  unfold MaximumCall622Leaf130ValueFrom608.depth_value.
  now rewrite MaximumCall622Leaf130ValueFrom608.values_eq.
Qed.

Definition value := Eval vm_compute in MaximumCall622Leaf130ValueFrom608.depth_value.
Lemma value_eq : MaximumCall622Via595ContextFrom608.depth MaximumCall622Leaf130ContextFrom608.outer = value.
Proof.
  rewrite depth_cached.
  vm_cast_no_check (eq_refl value).
Qed.
