From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall875Context MaximumCall875Leaf01Split MaximumCall874Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall875Context.funs MaximumCall875Context.callee
    [MaximumCall875Context.callee] (sptree.size MaximumContext.funs)
    874 MaximumCall875Leaf01Split.ret_data MaximumCall875Leaf01Split.handler_data
    MaximumCall874Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall875Context.depth MaximumCall875Leaf01Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall875Leaf01Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall875Leaf01Split.callee_body_depth,
    MaximumCall874Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall874Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall875Context.depth MaximumCall875Leaf01Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
