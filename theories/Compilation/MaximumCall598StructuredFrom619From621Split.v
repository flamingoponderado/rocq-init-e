From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall598Via599From619From621Context MaximumCall598StructuredFrom619From621Context.

Lemma body_depth_split :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall598Via599From619From621Context.funs
      MaximumCall598Via599From619From621Context.callee [MaximumCall598Via599From619From621Context.callee]
      (sptree.size MaximumContext.funs) MaximumCall598Via599From619From621Context.body) =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall598StructuredFrom619From621Context.depth MaximumCall598StructuredFrom619From621Context.leaves).
Proof.
  unfold MaximumCall598StructuredFrom619From621Context.depth, MaximumCall598Via599From619From621Context.depth, MaximumCall598StructuredFrom619From621Context.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
