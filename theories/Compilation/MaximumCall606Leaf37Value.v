From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall606Via625Context MaximumCall606Leaf37Split MaximumCall602Via606Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall606Via625Context.funs MaximumCall606Via625Context.callee
    [MaximumCall606Via625Context.callee] (sptree.size MaximumContext.funs)
    602 MaximumCall606Leaf37Split.ret_data MaximumCall606Leaf37Split.handler_data
    MaximumCall602Via606Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall606Via625Context.depth MaximumCall606Leaf37Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall606Leaf37Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall606Leaf37Split.callee_body_depth,
    MaximumCall602Via606Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall602Via606Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall606Via625Context.depth MaximumCall606Leaf37Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
