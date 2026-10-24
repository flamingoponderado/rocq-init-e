From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall608Via625Context MaximumCall608Leaf15Split MaximumCall606Via608Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall608Via625Context.funs MaximumCall608Via625Context.callee
    [MaximumCall608Via625Context.callee] (sptree.size MaximumContext.funs)
    606 MaximumCall608Leaf15Split.ret_data MaximumCall608Leaf15Split.handler_data
    MaximumCall606Via608Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall608Via625Context.depth MaximumCall608Leaf15Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall608Leaf15Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall608Leaf15Split.callee_body_depth,
    MaximumCall606Via608Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall606Via608Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall608Via625Context.depth MaximumCall608Leaf15Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
