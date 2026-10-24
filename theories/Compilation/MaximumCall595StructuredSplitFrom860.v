From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall595Via602ContextFrom860 MaximumCall595StructuredContextFrom860.

Lemma body_depth_split :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall595Via602ContextFrom860.funs
      MaximumCall595Via602ContextFrom860.callee [MaximumCall595Via602ContextFrom860.callee]
      (sptree.size MaximumContext.funs) MaximumCall595Via602ContextFrom860.body) =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall595StructuredContextFrom860.depth MaximumCall595StructuredContextFrom860.leaves).
Proof.
  unfold MaximumCall595StructuredContextFrom860.depth, MaximumCall595Via602ContextFrom860.depth,
    MaximumCall595StructuredContextFrom860.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
