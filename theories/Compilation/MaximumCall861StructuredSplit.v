From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall861Via867Context MaximumCall861StructuredContext.

Lemma body_depth_split :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall861Via867Context.funs
      MaximumCall861Via867Context.callee [MaximumCall861Via867Context.callee]
      (sptree.size MaximumContext.funs) MaximumCall861Via867Context.body) =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall861StructuredContext.depth MaximumCall861StructuredContext.leaves).
Proof.
  unfold MaximumCall861StructuredContext.depth, MaximumCall861Via867Context.depth, MaximumCall861StructuredContext.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
