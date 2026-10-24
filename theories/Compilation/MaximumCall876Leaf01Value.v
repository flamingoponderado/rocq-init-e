From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall876Context MaximumCall876Leaf01Split MaximumCall875Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall876Context.funs MaximumCall876Context.callee
    [MaximumCall876Context.callee] (sptree.size MaximumContext.funs)
    875 MaximumCall876Leaf01Split.ret_data MaximumCall876Leaf01Split.handler_data
    MaximumCall875Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall876Context.depth MaximumCall876Leaf01Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall876Leaf01Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall876Leaf01Split.callee_body_depth,
    MaximumCall875Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall875Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall876Context.depth MaximumCall876Leaf01Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
