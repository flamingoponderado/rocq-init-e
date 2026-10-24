From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall622Leaf130Context MaximumCall622Inner54Split MaximumCall619Via622Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall622Leaf130Context.funs MaximumCall622Leaf130Context.callee
    [MaximumCall622Leaf130Context.callee] (sptree.size MaximumContext.funs)
    619 MaximumCall622Inner54Split.ret_data MaximumCall622Inner54Split.handler_data
    MaximumCall619Via622Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall622Leaf130Context.depth MaximumCall622Inner54Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall622Inner54Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall622Inner54Split.callee_body_depth,
    MaximumCall619Via622Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall619Via622Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall622Leaf130Context.depth MaximumCall622Inner54Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
