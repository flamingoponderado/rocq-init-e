From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall595StructuredContextFrom860 MaximumCall595Leaf1067SplitFrom860 MaximumCall624Via595ValueFrom860.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall595StructuredContextFrom860.funs MaximumCall595StructuredContextFrom860.callee
    [MaximumCall595StructuredContextFrom860.callee] (sptree.size MaximumContext.funs)
    624 MaximumCall595Leaf1067SplitFrom860.ret_data MaximumCall595Leaf1067SplitFrom860.handler_data
    MaximumCall624Via595ValueFrom860.depth_value.

Lemma cached_depth_eq :
  MaximumCall595StructuredContextFrom860.depth MaximumCall595Leaf1067SplitFrom860.leaf = cached_depth.
Proof.
  rewrite MaximumCall595Leaf1067SplitFrom860.leaf_depth_compact.
  unfold cached_depth, MaximumCall595Leaf1067SplitFrom860.callee_body_depth,
    MaximumCall624Via595ValueFrom860.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall624Via595ValueFrom860.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall595StructuredContextFrom860.depth MaximumCall595Leaf1067SplitFrom860.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
