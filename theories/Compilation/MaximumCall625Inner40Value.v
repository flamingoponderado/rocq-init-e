From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall625Leaf13Context MaximumCall625Inner40Split MaximumCall608Via625Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall625Leaf13Context.funs MaximumCall625Leaf13Context.callee
    [MaximumCall625Leaf13Context.callee] (sptree.size MaximumContext.funs)
    608 MaximumCall625Inner40Split.ret_data MaximumCall625Inner40Split.handler_data
    MaximumCall608Via625Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall625Leaf13Context.depth MaximumCall625Inner40Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall625Inner40Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall625Inner40Split.callee_body_depth,
    MaximumCall608Via625Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall608Via625Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall625Leaf13Context.depth MaximumCall625Inner40Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
