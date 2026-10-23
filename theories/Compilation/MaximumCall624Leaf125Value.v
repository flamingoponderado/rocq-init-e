From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall624Via595Context MaximumCall624Leaf125Split MaximumCall619Via624Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall624Via595Context.funs MaximumCall624Via595Context.callee
    [MaximumCall624Via595Context.callee] (sptree.size MaximumContext.funs)
    619 MaximumCall624Leaf125Split.ret_data MaximumCall624Leaf125Split.handler_data
    MaximumCall619Via624Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall624Via595Context.depth MaximumCall624Leaf125Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall624Leaf125Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall624Leaf125Split.callee_body_depth,
    MaximumCall619Via624Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall619Via624Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall624Via595Context.depth MaximumCall624Leaf125Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
