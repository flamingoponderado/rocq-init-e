From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall625Via863Context MaximumCall625Leaf13Context.

Lemma outer_depth_split :
  MaximumCall625Via863Context.depth MaximumCall625Leaf13Context.outer =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall625Leaf13Context.depth MaximumCall625Leaf13Context.leaves).
Proof.
  unfold MaximumCall625Via863Context.depth,
    MaximumCall625Leaf13Context.depth, MaximumCall625Leaf13Context.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
