From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall863Via868Context MaximumCall863Leaf367Split MaximumCall625Via863Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall863Via868Context.funs MaximumCall863Via868Context.callee
    [MaximumCall863Via868Context.callee] (sptree.size MaximumContext.funs)
    625 MaximumCall863Leaf367Split.ret_data MaximumCall863Leaf367Split.handler_data
    MaximumCall625Via863Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall863Via868Context.depth MaximumCall863Leaf367Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall863Leaf367Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall863Leaf367Split.callee_body_depth,
    MaximumCall625Via863Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall625Via863Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall863Via868Context.depth MaximumCall863Leaf367Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
