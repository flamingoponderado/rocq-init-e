From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall595Via602ContextFrom608From860 MaximumCall595StructuredContextFrom608From860.

Lemma body_depth_split :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall595Via602ContextFrom608From860.funs
      MaximumCall595Via602ContextFrom608From860.callee [MaximumCall595Via602ContextFrom608From860.callee]
      (sptree.size MaximumContext.funs) MaximumCall595Via602ContextFrom608From860.body) =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall595StructuredContextFrom608From860.depth MaximumCall595StructuredContextFrom608From860.leaves).
Proof.
  unfold MaximumCall595StructuredContextFrom608From860.depth, MaximumCall595Via602ContextFrom608From860.depth,
    MaximumCall595StructuredContextFrom608From860.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
