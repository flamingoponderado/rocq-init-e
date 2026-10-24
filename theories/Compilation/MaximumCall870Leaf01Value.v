From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall870Context MaximumCall870Leaf01Split MaximumCall869FullValue.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall870Context.funs MaximumCall870Context.callee
    [MaximumCall870Context.callee] (sptree.size MaximumContext.funs)
    869 MaximumCall870Leaf01Split.ret_data MaximumCall870Leaf01Split.handler_data
    MaximumCall869FullValue.depth_value.

Lemma cached_depth_eq :
  MaximumCall870Context.depth MaximumCall870Leaf01Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall870Leaf01Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall870Leaf01Split.callee_body_depth,
    MaximumCall869FullValue.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall869FullValue.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall870Context.depth MaximumCall870Leaf01Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
