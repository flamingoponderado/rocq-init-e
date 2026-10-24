From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall837Via598From619From622ContextFrom860 MaximumCall837StructuredFrom598From619From622ContextFrom860.

Lemma body_depth_split :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall837Via598From619From622ContextFrom860.funs
      MaximumCall837Via598From619From622ContextFrom860.callee [MaximumCall837Via598From619From622ContextFrom860.callee]
      (sptree.size MaximumContext.funs) MaximumCall837Via598From619From622ContextFrom860.body) =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall837StructuredFrom598From619From622ContextFrom860.depth MaximumCall837StructuredFrom598From619From622ContextFrom860.leaves).
Proof.
  unfold MaximumCall837StructuredFrom598From619From622ContextFrom860.depth, MaximumCall837Via598From619From622ContextFrom860.depth, MaximumCall837StructuredFrom598From619From622ContextFrom860.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
