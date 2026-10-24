From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall877Context MaximumCall877Leaf03Split MaximumCall876Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall877Context.funs MaximumCall877Context.callee
    [MaximumCall877Context.callee] (sptree.size MaximumContext.funs)
    876 MaximumCall877Leaf03Split.ret_data MaximumCall877Leaf03Split.handler_data
    MaximumCall876Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall877Context.depth MaximumCall877Leaf03Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall877Leaf03Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall877Leaf03Split.callee_body_depth,
    MaximumCall876Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall876Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall877Context.depth MaximumCall877Leaf03Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
