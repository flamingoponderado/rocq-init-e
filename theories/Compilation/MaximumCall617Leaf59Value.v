From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall617Via595Context MaximumCall617Leaf59Split MaximumCall616Via617Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall617Via595Context.funs MaximumCall617Via595Context.callee
    [MaximumCall617Via595Context.callee] (sptree.size MaximumContext.funs)
    616 MaximumCall617Leaf59Split.ret_data MaximumCall617Leaf59Split.handler_data
    MaximumCall616Via617Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall617Via595Context.depth MaximumCall617Leaf59Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall617Leaf59Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall617Leaf59Split.callee_body_depth,
    MaximumCall616Via617Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall616Via617Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall617Via595Context.depth MaximumCall617Leaf59Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
