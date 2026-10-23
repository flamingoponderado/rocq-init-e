From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall619Via622Context MaximumCall619From622Leaf42Split MaximumCall603Via619From622Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall619Via622Context.funs MaximumCall619Via622Context.callee
    [MaximumCall619Via622Context.callee] (sptree.size MaximumContext.funs)
    603 MaximumCall619From622Leaf42Split.ret_data MaximumCall619From622Leaf42Split.handler_data
    MaximumCall603Via619From622Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall619Via622Context.depth MaximumCall619From622Leaf42Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall619From622Leaf42Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall619From622Leaf42Split.callee_body_depth,
    MaximumCall603Via619From622Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall603Via619From622Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall619Via622Context.depth MaximumCall619From622Leaf42Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
