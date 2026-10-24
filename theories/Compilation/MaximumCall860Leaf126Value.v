From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall860Via868Context MaximumCall860Leaf126Split MaximumCall625Via860Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall860Via868Context.funs MaximumCall860Via868Context.callee
    [MaximumCall860Via868Context.callee] (sptree.size MaximumContext.funs)
    625 MaximumCall860Leaf126Split.ret_data MaximumCall860Leaf126Split.handler_data
    MaximumCall625Via860Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall860Via868Context.depth MaximumCall860Leaf126Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall860Leaf126Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall860Leaf126Split.callee_body_depth,
    MaximumCall625Via860Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall625Via860Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall860Via868Context.depth MaximumCall860Leaf126Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
