From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall598Via599From619From621ContextFrom608 MaximumCall598StructuredFrom619From621ContextFrom608.

Lemma body_depth_split :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall598Via599From619From621ContextFrom608.funs
      MaximumCall598Via599From619From621ContextFrom608.callee [MaximumCall598Via599From619From621ContextFrom608.callee]
      (sptree.size MaximumContext.funs) MaximumCall598Via599From619From621ContextFrom608.body) =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall598StructuredFrom619From621ContextFrom608.depth MaximumCall598StructuredFrom619From621ContextFrom608.leaves).
Proof.
  unfold MaximumCall598StructuredFrom619From621ContextFrom608.depth, MaximumCall598Via599From619From621ContextFrom608.depth, MaximumCall598StructuredFrom619From621ContextFrom608.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
