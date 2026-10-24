From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall860Via861Context MaximumCall860Leaf126SplitFrom861 MaximumCall625Via860ValueFrom861.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall860Via861Context.funs MaximumCall860Via861Context.callee
    [MaximumCall860Via861Context.callee] (sptree.size MaximumContext.funs)
    625 MaximumCall860Leaf126SplitFrom861.ret_data MaximumCall860Leaf126SplitFrom861.handler_data
    MaximumCall625Via860ValueFrom861.depth_value.

Lemma cached_depth_eq :
  MaximumCall860Via861Context.depth MaximumCall860Leaf126SplitFrom861.leaf = cached_depth.
Proof.
  rewrite MaximumCall860Leaf126SplitFrom861.leaf_depth_compact.
  unfold cached_depth, MaximumCall860Leaf126SplitFrom861.callee_body_depth,
    MaximumCall625Via860ValueFrom861.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall625Via860ValueFrom861.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall860Via861Context.depth MaximumCall860Leaf126SplitFrom861.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
