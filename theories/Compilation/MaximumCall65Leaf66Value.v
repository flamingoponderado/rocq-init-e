From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum MaximumContext
  MaximumCall65Context MaximumCall65Leaf66Split MaximumCall877Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumContext.funs MaximumCall65Context.callee
    [MaximumCall65Context.callee; MaximumContext.root]
    (sptree.size MaximumContext.funs) 877
    MaximumCall65Leaf66Split.ret_data MaximumCall65Leaf66Split.handler_data
    MaximumCall877Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall65Context.depth MaximumCall65Leaf66Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall65Leaf66Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall65Leaf66Split.callee_body_depth,
    MaximumCall877Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall877Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq :
  MaximumCall65Context.depth MaximumCall65Leaf66Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
