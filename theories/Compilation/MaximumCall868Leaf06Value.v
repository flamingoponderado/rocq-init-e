From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall868Context MaximumCall868Leaf06Split MaximumCall68Via868Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall868Context.funs MaximumCall868Context.callee
    [MaximumCall868Context.callee] (sptree.size MaximumContext.funs)
    68 MaximumCall868Leaf06Split.ret_data MaximumCall868Leaf06Split.handler_data
    MaximumCall68Via868Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall868Context.depth MaximumCall868Leaf06Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall868Leaf06Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall868Leaf06Split.callee_body_depth,
    MaximumCall68Via868Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall68Via868Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall868Context.depth MaximumCall868Leaf06Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
