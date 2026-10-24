From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall608Via625ContextFrom860From861 MaximumCall608Leaf15SplitFrom860From861 MaximumCall606Via608ValueFrom860From861.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall608Via625ContextFrom860From861.funs MaximumCall608Via625ContextFrom860From861.callee
    [MaximumCall608Via625ContextFrom860From861.callee] (sptree.size MaximumContext.funs)
    606 MaximumCall608Leaf15SplitFrom860From861.ret_data MaximumCall608Leaf15SplitFrom860From861.handler_data
    MaximumCall606Via608ValueFrom860From861.depth_value.

Lemma cached_depth_eq :
  MaximumCall608Via625ContextFrom860From861.depth MaximumCall608Leaf15SplitFrom860From861.leaf = cached_depth.
Proof.
  rewrite MaximumCall608Leaf15SplitFrom860From861.leaf_depth_compact.
  unfold cached_depth, MaximumCall608Leaf15SplitFrom860From861.callee_body_depth,
    MaximumCall606Via608ValueFrom860From861.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall606Via608ValueFrom860From861.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall608Via625ContextFrom860From861.depth MaximumCall608Leaf15SplitFrom860From861.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
