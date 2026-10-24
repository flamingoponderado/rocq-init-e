From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall623Via595ContextFrom608From860 MaximumCall623Leaf131SplitFrom608From860 MaximumCall619Via623ValueFrom608From860.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall623Via595ContextFrom608From860.funs MaximumCall623Via595ContextFrom608From860.callee
    [MaximumCall623Via595ContextFrom608From860.callee] (sptree.size MaximumContext.funs)
    619 MaximumCall623Leaf131SplitFrom608From860.ret_data MaximumCall623Leaf131SplitFrom608From860.handler_data
    MaximumCall619Via623ValueFrom608From860.depth_value.

Lemma cached_depth_eq :
  MaximumCall623Via595ContextFrom608From860.depth MaximumCall623Leaf131SplitFrom608From860.leaf = cached_depth.
Proof.
  rewrite MaximumCall623Leaf131SplitFrom608From860.leaf_depth_compact.
  unfold cached_depth, MaximumCall623Leaf131SplitFrom608From860.callee_body_depth,
    MaximumCall619Via623ValueFrom608From860.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall619Via623ValueFrom608From860.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall623Via595ContextFrom608From860.depth MaximumCall623Leaf131SplitFrom608From860.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
