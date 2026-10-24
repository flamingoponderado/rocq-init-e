From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import FastMaximum MaximumContext MaximumRootValue.
Open Scope N_scope.

Lemma body_depth_eq :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumContext.funs MaximumContext.root
      [MaximumContext.root] (sptree.size MaximumContext.funs)
      MaximumContext.program) = MaximumRootValue.depth_value.
Proof.
  transitivity (FastMaximum.fast_depth MaximumContext.frames
    MaximumContext.funs MaximumContext.root [MaximumContext.root]
    (sptree.size MaximumContext.funs) MaximumContext.program).
  - symmetry; apply FastMaximum.fast_depth_exact.
  - rewrite FastMaximum.fast_depth_leaves.
    change (fold_right FastMaximum.join_depth (Some 0)
      (List.map MaximumContext.depth MaximumContext.leaves) =
      MaximumRootValue.depth_value).
    unfold MaximumRootValue.depth_value.
    now rewrite MaximumRootValue.values_eq.
Qed.
