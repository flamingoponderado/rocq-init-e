From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall865Via868Context MaximumCall865StructuredContext.

Lemma body_depth_split :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall865Via868Context.funs
      MaximumCall865Via868Context.callee [MaximumCall865Via868Context.callee]
      (sptree.size MaximumContext.funs) MaximumCall865Via868Context.body) =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall865StructuredContext.depth MaximumCall865StructuredContext.leaves).
Proof.
  unfold MaximumCall865StructuredContext.depth, MaximumCall865Via868Context.depth, MaximumCall865StructuredContext.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
