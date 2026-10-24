From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall602Via606ContextFrom608From860 MaximumCall602Leaf04ContextFrom608From860.

Lemma outer_depth_split :
  MaximumCall602Via606ContextFrom608From860.depth MaximumCall602Leaf04ContextFrom608From860.outer =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall602Leaf04ContextFrom608From860.depth MaximumCall602Leaf04ContextFrom608From860.leaves).
Proof.
  unfold MaximumCall602Via606ContextFrom608From860.depth,
    MaximumCall602Leaf04ContextFrom608From860.depth, MaximumCall602Leaf04ContextFrom608From860.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
