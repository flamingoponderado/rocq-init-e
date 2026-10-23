From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall603Via619From623Context MaximumCall603From619From623Leaf61Split MaximumCall599Via603From619From623Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall603Via619From623Context.funs MaximumCall603Via619From623Context.callee
    [MaximumCall603Via619From623Context.callee] (sptree.size MaximumContext.funs)
    599 MaximumCall603From619From623Leaf61Split.ret_data MaximumCall603From619From623Leaf61Split.handler_data
    MaximumCall599Via603From619From623Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall603Via619From623Context.depth MaximumCall603From619From623Leaf61Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall603From619From623Leaf61Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall603From619From623Leaf61Split.callee_body_depth,
    MaximumCall599Via603From619From623Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall599Via603From619From623Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall603Via619From623Context.depth MaximumCall603From619From623Leaf61Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
