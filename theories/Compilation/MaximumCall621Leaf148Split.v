From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall621Via595Context MaximumCall621Leaf148Context.

Lemma outer_depth_split :
  MaximumCall621Via595Context.depth MaximumCall621Leaf148Context.outer =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall621Leaf148Context.depth MaximumCall621Leaf148Context.leaves).
Proof.
  unfold MaximumCall621Via595Context.depth, MaximumCall621Leaf148Context.depth, MaximumCall621Leaf148Context.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
