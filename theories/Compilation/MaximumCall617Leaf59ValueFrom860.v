From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall617Via595ContextFrom860 MaximumCall617Leaf59SplitFrom860 MaximumCall616Via617ValueFrom860.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall617Via595ContextFrom860.funs MaximumCall617Via595ContextFrom860.callee
    [MaximumCall617Via595ContextFrom860.callee] (sptree.size MaximumContext.funs)
    616 MaximumCall617Leaf59SplitFrom860.ret_data MaximumCall617Leaf59SplitFrom860.handler_data
    MaximumCall616Via617ValueFrom860.depth_value.

Lemma cached_depth_eq :
  MaximumCall617Via595ContextFrom860.depth MaximumCall617Leaf59SplitFrom860.leaf = cached_depth.
Proof.
  rewrite MaximumCall617Leaf59SplitFrom860.leaf_depth_compact.
  unfold cached_depth, MaximumCall617Leaf59SplitFrom860.callee_body_depth,
    MaximumCall616Via617ValueFrom860.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall616Via617ValueFrom860.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall617Via595ContextFrom860.depth MaximumCall617Leaf59SplitFrom860.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
