From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall602Via606Context MaximumCall602Leaf04Context.

Lemma outer_depth_split :
  MaximumCall602Via606Context.depth MaximumCall602Leaf04Context.outer =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall602Leaf04Context.depth MaximumCall602Leaf04Context.leaves).
Proof.
  unfold MaximumCall602Via606Context.depth,
    MaximumCall602Leaf04Context.depth, MaximumCall602Leaf04Context.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
