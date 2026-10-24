From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall868SuffixContext MaximumCall868SuffixLeaf109Split MaximumCall387Via868Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall868SuffixContext.funs MaximumCall868SuffixContext.callee
    [MaximumCall868SuffixContext.callee] (sptree.size MaximumContext.funs)
    387 MaximumCall868SuffixLeaf109Split.ret_data MaximumCall868SuffixLeaf109Split.handler_data
    MaximumCall387Via868Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall868SuffixContext.depth MaximumCall868SuffixLeaf109Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall868SuffixLeaf109Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall868SuffixLeaf109Split.callee_body_depth,
    MaximumCall387Via868Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall387Via868Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall868SuffixContext.depth MaximumCall868SuffixLeaf109Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
