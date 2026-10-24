From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall872Context MaximumCall872Leaf01Split MaximumCall871Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall872Context.funs MaximumCall872Context.callee
    [MaximumCall872Context.callee] (sptree.size MaximumContext.funs)
    871 MaximumCall872Leaf01Split.ret_data MaximumCall872Leaf01Split.handler_data
    MaximumCall871Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall872Context.depth MaximumCall872Leaf01Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall872Leaf01Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall872Leaf01Split.callee_body_depth,
    MaximumCall871Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall871Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall872Context.depth MaximumCall872Leaf01Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
