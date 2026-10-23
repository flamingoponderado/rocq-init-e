From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall595StructuredContext MaximumCall595Leaf1067Split MaximumCall624Via595Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall595StructuredContext.funs MaximumCall595StructuredContext.callee
    [MaximumCall595StructuredContext.callee] (sptree.size MaximumContext.funs)
    624 MaximumCall595Leaf1067Split.ret_data MaximumCall595Leaf1067Split.handler_data
    MaximumCall624Via595Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall595StructuredContext.depth MaximumCall595Leaf1067Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall595Leaf1067Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall595Leaf1067Split.callee_body_depth,
    MaximumCall624Via595Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall624Via595Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall595StructuredContext.depth MaximumCall595Leaf1067Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
