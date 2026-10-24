From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall873Context MaximumCall873Leaf01Split MaximumCall872Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall873Context.funs MaximumCall873Context.callee
    [MaximumCall873Context.callee] (sptree.size MaximumContext.funs)
    872 MaximumCall873Leaf01Split.ret_data MaximumCall873Leaf01Split.handler_data
    MaximumCall872Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall873Context.depth MaximumCall873Leaf01Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall873Leaf01Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall873Leaf01Split.callee_body_depth,
    MaximumCall872Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall872Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall873Context.depth MaximumCall873Leaf01Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
