From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall621Via595ContextFrom608From860 MaximumCall621Leaf148ContextFrom608From860.

Lemma outer_depth_split :
  MaximumCall621Via595ContextFrom608From860.depth MaximumCall621Leaf148ContextFrom608From860.outer =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall621Leaf148ContextFrom608From860.depth MaximumCall621Leaf148ContextFrom608From860.leaves).
Proof.
  unfold MaximumCall621Via595ContextFrom608From860.depth, MaximumCall621Leaf148ContextFrom608From860.depth, MaximumCall621Leaf148ContextFrom608From860.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
