From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall622Leaf130ContextFrom608From860From861 MaximumCall622Inner54SplitFrom608From860From861 MaximumCall619Via622ValueFrom608From860From861.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall622Leaf130ContextFrom608From860From861.funs MaximumCall622Leaf130ContextFrom608From860From861.callee
    [MaximumCall622Leaf130ContextFrom608From860From861.callee] (sptree.size MaximumContext.funs)
    619 MaximumCall622Inner54SplitFrom608From860From861.ret_data MaximumCall622Inner54SplitFrom608From860From861.handler_data
    MaximumCall619Via622ValueFrom608From860From861.depth_value.

Lemma cached_depth_eq :
  MaximumCall622Leaf130ContextFrom608From860From861.depth MaximumCall622Inner54SplitFrom608From860From861.leaf = cached_depth.
Proof.
  rewrite MaximumCall622Inner54SplitFrom608From860From861.leaf_depth_compact.
  unfold cached_depth, MaximumCall622Inner54SplitFrom608From860From861.callee_body_depth,
    MaximumCall619Via622ValueFrom608From860From861.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall619Via622ValueFrom608From860From861.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall622Leaf130ContextFrom608From860From861.depth MaximumCall622Inner54SplitFrom608From860From861.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
