From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall623Via595Context MaximumCall623Leaf131Split MaximumCall619Via623Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall623Via595Context.funs MaximumCall623Via595Context.callee
    [MaximumCall623Via595Context.callee] (sptree.size MaximumContext.funs)
    619 MaximumCall623Leaf131Split.ret_data MaximumCall623Leaf131Split.handler_data
    MaximumCall619Via623Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall623Via595Context.depth MaximumCall623Leaf131Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall623Leaf131Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall623Leaf131Split.callee_body_depth,
    MaximumCall619Via623Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall619Via623Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall623Via595Context.depth MaximumCall623Leaf131Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
