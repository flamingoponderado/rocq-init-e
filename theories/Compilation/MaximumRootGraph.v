From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import MaximumContext MaximumRootLookup.
Open Scope N_scope.

Lemma full_graph_eq :
  word_depth.full_call_graph MaximumContext.root MaximumContext.funs =
  word_depth.Branch (word_depth.Call MaximumContext.root word_depth.Leaf)
    (word_depth.call_graph MaximumContext.funs MaximumContext.root
      [MaximumContext.root] (sptree.size MaximumContext.funs)
      MaximumContext.program).
Proof.
  unfold word_depth.full_call_graph.
  rewrite MaximumRootLookup.root_lookup.
  reflexivity.
Qed.
