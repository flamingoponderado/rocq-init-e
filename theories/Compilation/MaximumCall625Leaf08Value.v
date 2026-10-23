From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall625Via863Context MaximumCall625Leaf08Split
  MaximumCall78Via625Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall625Via863Context.funs MaximumCall625Via863Context.callee
    [MaximumCall625Via863Context.callee] (sptree.size MaximumContext.funs)
    78 MaximumCall625Leaf08Split.ret_data
    MaximumCall625Leaf08Split.handler_data
    MaximumCall78Via625Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall625Via863Context.depth MaximumCall625Leaf08Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall625Leaf08Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall625Leaf08Split.callee_body_depth,
    MaximumCall78Via625Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall78Via625Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq :
  MaximumCall625Via863Context.depth MaximumCall625Leaf08Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
