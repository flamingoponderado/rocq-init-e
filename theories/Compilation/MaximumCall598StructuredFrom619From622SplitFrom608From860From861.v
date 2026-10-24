From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall598Via599From619From622ContextFrom608From860From861 MaximumCall598StructuredFrom619From622ContextFrom608From860From861.

Lemma body_depth_split :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall598Via599From619From622ContextFrom608From860From861.funs
      MaximumCall598Via599From619From622ContextFrom608From860From861.callee [MaximumCall598Via599From619From622ContextFrom608From860From861.callee]
      (sptree.size MaximumContext.funs) MaximumCall598Via599From619From622ContextFrom608From860From861.body) =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall598StructuredFrom619From622ContextFrom608From860From861.depth MaximumCall598StructuredFrom619From622ContextFrom608From860From861.leaves).
Proof.
  unfold MaximumCall598StructuredFrom619From622ContextFrom608From860From861.depth, MaximumCall598Via599From619From622ContextFrom608From860From861.depth, MaximumCall598StructuredFrom619From622ContextFrom608From860From861.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
