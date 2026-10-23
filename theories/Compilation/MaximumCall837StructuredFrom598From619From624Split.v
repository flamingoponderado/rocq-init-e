From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall837Via598From619From624Context MaximumCall837StructuredFrom598From619From624Context.

Lemma body_depth_split :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall837Via598From619From624Context.funs
      MaximumCall837Via598From619From624Context.callee [MaximumCall837Via598From619From624Context.callee]
      (sptree.size MaximumContext.funs) MaximumCall837Via598From619From624Context.body) =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall837StructuredFrom598From619From624Context.depth MaximumCall837StructuredFrom598From619From624Context.leaves).
Proof.
  unfold MaximumCall837StructuredFrom598From619From624Context.depth, MaximumCall837Via598From619From624Context.depth, MaximumCall837StructuredFrom598From619From624Context.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
