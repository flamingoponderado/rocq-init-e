From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall624Via595ContextFrom608 MaximumCall624Leaf125SplitFrom608 MaximumCall619Via624ValueFrom608.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall624Via595ContextFrom608.funs MaximumCall624Via595ContextFrom608.callee
    [MaximumCall624Via595ContextFrom608.callee] (sptree.size MaximumContext.funs)
    619 MaximumCall624Leaf125SplitFrom608.ret_data MaximumCall624Leaf125SplitFrom608.handler_data
    MaximumCall619Via624ValueFrom608.depth_value.

Lemma cached_depth_eq :
  MaximumCall624Via595ContextFrom608.depth MaximumCall624Leaf125SplitFrom608.leaf = cached_depth.
Proof.
  rewrite MaximumCall624Leaf125SplitFrom608.leaf_depth_compact.
  unfold cached_depth, MaximumCall624Leaf125SplitFrom608.callee_body_depth,
    MaximumCall619Via624ValueFrom608.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall619Via624ValueFrom608.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall624Via595ContextFrom608.depth MaximumCall624Leaf125SplitFrom608.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
