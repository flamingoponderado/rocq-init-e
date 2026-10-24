From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall625Via860Context MaximumCall625Leaf13ContextFrom860.

Lemma outer_depth_split :
  MaximumCall625Via860Context.depth MaximumCall625Leaf13ContextFrom860.outer =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall625Leaf13ContextFrom860.depth MaximumCall625Leaf13ContextFrom860.leaves).
Proof.
  unfold MaximumCall625Via860Context.depth,
    MaximumCall625Leaf13ContextFrom860.depth, MaximumCall625Leaf13ContextFrom860.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
