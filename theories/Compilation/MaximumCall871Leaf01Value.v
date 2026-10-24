From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall871Context MaximumCall871Leaf01Split MaximumCall870Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall871Context.funs MaximumCall871Context.callee
    [MaximumCall871Context.callee] (sptree.size MaximumContext.funs)
    870 MaximumCall871Leaf01Split.ret_data MaximumCall871Leaf01Split.handler_data
    MaximumCall870Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall871Context.depth MaximumCall871Leaf01Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall871Leaf01Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall871Leaf01Split.callee_body_depth,
    MaximumCall870Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall870Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall871Context.depth MaximumCall871Leaf01Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
