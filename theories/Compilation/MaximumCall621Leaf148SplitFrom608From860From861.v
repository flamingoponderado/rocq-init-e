From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall621Via595ContextFrom608From860From861 MaximumCall621Leaf148ContextFrom608From860From861.

Lemma outer_depth_split :
  MaximumCall621Via595ContextFrom608From860From861.depth MaximumCall621Leaf148ContextFrom608From860From861.outer =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall621Leaf148ContextFrom608From860From861.depth MaximumCall621Leaf148ContextFrom608From860From861.leaves).
Proof.
  unfold MaximumCall621Via595ContextFrom608From860From861.depth, MaximumCall621Leaf148ContextFrom608From860From861.depth, MaximumCall621Leaf148ContextFrom608From860From861.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
