From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall595Via602Context MaximumCall595StructuredContext.

Lemma body_depth_split :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall595Via602Context.funs
      MaximumCall595Via602Context.callee [MaximumCall595Via602Context.callee]
      (sptree.size MaximumContext.funs) MaximumCall595Via602Context.body) =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall595StructuredContext.depth MaximumCall595StructuredContext.leaves).
Proof.
  unfold MaximumCall595StructuredContext.depth, MaximumCall595Via602Context.depth,
    MaximumCall595StructuredContext.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
