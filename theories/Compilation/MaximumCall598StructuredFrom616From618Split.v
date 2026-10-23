From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall598Via599From616From618Context MaximumCall598StructuredFrom616From618Context.

Lemma body_depth_split :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall598Via599From616From618Context.funs
      MaximumCall598Via599From616From618Context.callee [MaximumCall598Via599From616From618Context.callee]
      (sptree.size MaximumContext.funs) MaximumCall598Via599From616From618Context.body) =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall598StructuredFrom616From618Context.depth MaximumCall598StructuredFrom616From618Context.leaves).
Proof.
  unfold MaximumCall598StructuredFrom616From618Context.depth, MaximumCall598Via599From616From618Context.depth, MaximumCall598StructuredFrom616From618Context.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
