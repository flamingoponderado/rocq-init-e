From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.cakeml.compiler.backend Require Import word_depth wordLang.
From InitE.Compilation Require Import CallDepthLemma MaximumContext MaximumCall65Context MaximumRootLeaf339Callee.
Open Scope N_scope.

Lemma leaf_depth_split :
  MaximumContext.depth leaf =
  OPTION_MAP2 MAX
    (word_depth.max_depth MaximumContext.frames (word_depth.Call 65 word_depth.Leaf))
    callee_body_depth.
Proof.
  unfold MaximumContext.depth.
  rewrite leaf_shape.
  etransitivity.
  - apply (CallDepthLemma.max_depth_noret_call
      MaximumContext.frames MaximumContext.funs MaximumContext.root
      [MaximumContext.root] (sptree.size MaximumContext.funs)
      65 args None argc MaximumCall65Context.body);
      [exact not_visited | exact body_lookup | exact enough_fuel].
  - now rewrite callee_body_depth_eq.
Qed.

