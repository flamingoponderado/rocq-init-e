From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall618Via595Context MaximumCall618Leaf75Split MaximumCall616Via618Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall618Via595Context.funs MaximumCall618Via595Context.callee
    [MaximumCall618Via595Context.callee] (sptree.size MaximumContext.funs)
    616 MaximumCall618Leaf75Split.ret_data MaximumCall618Leaf75Split.handler_data
    MaximumCall616Via618Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall618Via595Context.depth MaximumCall618Leaf75Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall618Leaf75Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall618Leaf75Split.callee_body_depth,
    MaximumCall616Via618Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall616Via618Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall618Via595Context.depth MaximumCall618Leaf75Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
