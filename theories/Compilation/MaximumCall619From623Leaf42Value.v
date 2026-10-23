From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall619Via623Context MaximumCall619From623Leaf42Split MaximumCall603Via619From623Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall619Via623Context.funs MaximumCall619Via623Context.callee
    [MaximumCall619Via623Context.callee] (sptree.size MaximumContext.funs)
    603 MaximumCall619From623Leaf42Split.ret_data MaximumCall619From623Leaf42Split.handler_data
    MaximumCall603Via619From623Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall619Via623Context.depth MaximumCall619From623Leaf42Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall619From623Leaf42Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall619From623Leaf42Split.callee_body_depth,
    MaximumCall603Via619From623Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall603Via619From623Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall619Via623Context.depth MaximumCall619From623Leaf42Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
