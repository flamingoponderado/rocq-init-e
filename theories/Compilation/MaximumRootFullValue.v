From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.cakeml.compiler.backend Require Import word_depth.

From InitE.Compilation Require Import FastMaximum MaximumContext MaximumRootValue MaximumRootGraph MaximumRootBodyValue.
Open Scope N_scope.

Lemma max_depth_branch ss t1 t2 :
  word_depth.max_depth ss (word_depth.Branch t1 t2) =
  OPTION_MAP2 MAX (word_depth.max_depth ss t1) (word_depth.max_depth ss t2).
Proof. reflexivity. Qed.

Definition maximum := OPTION_MAP2 MAX
  (word_depth.max_depth MaximumContext.frames
    (word_depth.Call MaximumContext.root word_depth.Leaf))
  MaximumRootValue.depth_value.
Lemma maximum_eq :
  word_depth.max_depth MaximumContext.frames
    (word_depth.full_call_graph MaximumContext.root MaximumContext.funs) = maximum.
Proof.
  rewrite MaximumRootGraph.full_graph_eq.
  rewrite max_depth_branch.
  unfold maximum.
  now rewrite MaximumRootBodyValue.body_depth_eq.
Qed.
