From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall874Context MaximumCall874Leaf01Split MaximumCall873Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall874Context.funs MaximumCall874Context.callee
    [MaximumCall874Context.callee] (sptree.size MaximumContext.funs)
    873 MaximumCall874Leaf01Split.ret_data MaximumCall874Leaf01Split.handler_data
    MaximumCall873Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall874Context.depth MaximumCall874Leaf01Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall874Leaf01Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall874Leaf01Split.callee_body_depth,
    MaximumCall873Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall873Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall874Context.depth MaximumCall874Leaf01Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
