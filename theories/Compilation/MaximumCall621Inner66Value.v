From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall621Leaf148Context MaximumCall621Inner66Split MaximumCall619Via621Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall621Leaf148Context.funs MaximumCall621Leaf148Context.callee
    [MaximumCall621Leaf148Context.callee] (sptree.size MaximumContext.funs)
    619 MaximumCall621Inner66Split.ret_data MaximumCall621Inner66Split.handler_data
    MaximumCall619Via621Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall621Leaf148Context.depth MaximumCall621Inner66Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall621Inner66Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall621Inner66Split.callee_body_depth,
    MaximumCall619Via621Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall619Via621Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall621Leaf148Context.depth MaximumCall621Inner66Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
