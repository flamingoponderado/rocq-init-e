From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall621Leaf148ContextFrom860 MaximumCall621Inner66SplitFrom860 MaximumCall619Via621ValueFrom860.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall621Leaf148ContextFrom860.funs MaximumCall621Leaf148ContextFrom860.callee
    [MaximumCall621Leaf148ContextFrom860.callee] (sptree.size MaximumContext.funs)
    619 MaximumCall621Inner66SplitFrom860.ret_data MaximumCall621Inner66SplitFrom860.handler_data
    MaximumCall619Via621ValueFrom860.depth_value.

Lemma cached_depth_eq :
  MaximumCall621Leaf148ContextFrom860.depth MaximumCall621Inner66SplitFrom860.leaf = cached_depth.
Proof.
  rewrite MaximumCall621Inner66SplitFrom860.leaf_depth_compact.
  unfold cached_depth, MaximumCall621Inner66SplitFrom860.callee_body_depth,
    MaximumCall619Via621ValueFrom860.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall619Via621ValueFrom860.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall621Leaf148ContextFrom860.depth MaximumCall621Inner66SplitFrom860.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
