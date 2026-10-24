From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall625Leaf13ContextFrom860 MaximumCall625Inner40SplitFrom860 MaximumCall608Via625ValueFrom860.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall625Leaf13ContextFrom860.funs MaximumCall625Leaf13ContextFrom860.callee
    [MaximumCall625Leaf13ContextFrom860.callee] (sptree.size MaximumContext.funs)
    608 MaximumCall625Inner40SplitFrom860.ret_data MaximumCall625Inner40SplitFrom860.handler_data
    MaximumCall608Via625ValueFrom860.depth_value.

Lemma cached_depth_eq :
  MaximumCall625Leaf13ContextFrom860.depth MaximumCall625Inner40SplitFrom860.leaf = cached_depth.
Proof.
  rewrite MaximumCall625Inner40SplitFrom860.leaf_depth_compact.
  unfold cached_depth, MaximumCall625Inner40SplitFrom860.callee_body_depth,
    MaximumCall608Via625ValueFrom860.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall608Via625ValueFrom860.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall625Leaf13ContextFrom860.depth MaximumCall625Inner40SplitFrom860.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
