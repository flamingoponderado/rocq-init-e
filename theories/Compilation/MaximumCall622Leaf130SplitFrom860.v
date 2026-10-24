From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall622Via595ContextFrom860 MaximumCall622Leaf130ContextFrom860.

Lemma outer_depth_split :
  MaximumCall622Via595ContextFrom860.depth MaximumCall622Leaf130ContextFrom860.outer =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall622Leaf130ContextFrom860.depth MaximumCall622Leaf130ContextFrom860.leaves).
Proof.
  unfold MaximumCall622Via595ContextFrom860.depth, MaximumCall622Leaf130ContextFrom860.depth, MaximumCall622Leaf130ContextFrom860.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
