From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall867Via868Context MaximumCall867StructuredContext.

Lemma body_depth_split :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall867Via868Context.funs
      MaximumCall867Via868Context.callee [MaximumCall867Via868Context.callee]
      (sptree.size MaximumContext.funs) MaximumCall867Via868Context.body) =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall867StructuredContext.depth MaximumCall867StructuredContext.leaves).
Proof.
  unfold MaximumCall867StructuredContext.depth, MaximumCall867Via868Context.depth, MaximumCall867StructuredContext.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
