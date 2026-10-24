From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall868Loop120Context MaximumCall868Loop120Leaf13Split MaximumCall863Via868Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall868Loop120Context.funs MaximumCall868Loop120Context.callee
    [MaximumCall868Loop120Context.callee] (sptree.size MaximumContext.funs)
    863 MaximumCall868Loop120Leaf13Split.ret_data MaximumCall868Loop120Leaf13Split.handler_data
    MaximumCall863Via868Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall868Loop120Context.depth MaximumCall868Loop120Leaf13Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall868Loop120Leaf13Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall868Loop120Leaf13Split.callee_body_depth,
    MaximumCall863Via868Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall863Via868Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall868Loop120Context.depth MaximumCall868Loop120Leaf13Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
