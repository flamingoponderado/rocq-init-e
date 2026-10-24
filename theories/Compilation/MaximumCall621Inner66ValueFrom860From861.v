From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall621Leaf148ContextFrom860From861 MaximumCall621Inner66SplitFrom860From861 MaximumCall619Via621ValueFrom860From861.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall621Leaf148ContextFrom860From861.funs MaximumCall621Leaf148ContextFrom860From861.callee
    [MaximumCall621Leaf148ContextFrom860From861.callee] (sptree.size MaximumContext.funs)
    619 MaximumCall621Inner66SplitFrom860From861.ret_data MaximumCall621Inner66SplitFrom860From861.handler_data
    MaximumCall619Via621ValueFrom860From861.depth_value.

Lemma cached_depth_eq :
  MaximumCall621Leaf148ContextFrom860From861.depth MaximumCall621Inner66SplitFrom860From861.leaf = cached_depth.
Proof.
  rewrite MaximumCall621Inner66SplitFrom860From861.leaf_depth_compact.
  unfold cached_depth, MaximumCall621Inner66SplitFrom860From861.callee_body_depth,
    MaximumCall619Via621ValueFrom860From861.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall619Via621ValueFrom860From861.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall621Leaf148ContextFrom860From861.depth MaximumCall621Inner66SplitFrom860From861.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
