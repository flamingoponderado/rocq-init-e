From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall602Via606ContextFrom608 MaximumCall602Leaf04ContextFrom608.

Lemma outer_depth_split :
  MaximumCall602Via606ContextFrom608.depth MaximumCall602Leaf04ContextFrom608.outer =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall602Leaf04ContextFrom608.depth MaximumCall602Leaf04ContextFrom608.leaves).
Proof.
  unfold MaximumCall602Via606ContextFrom608.depth,
    MaximumCall602Leaf04ContextFrom608.depth, MaximumCall602Leaf04ContextFrom608.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
