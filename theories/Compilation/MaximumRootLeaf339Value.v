From Galette Require Import Base.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import MaximumContext MaximumCall65Value MaximumRootLeaf339Callee MaximumRootLeaf339Split.
Open Scope N_scope.

Definition cached_depth :=
  OPTION_MAP2 MAX
    (word_depth.max_depth MaximumContext.frames (word_depth.Call 65 word_depth.Leaf))
    MaximumCall65Value.depth_value.
Lemma cached_depth_eq : MaximumContext.depth leaf = cached_depth.
Proof.
  rewrite leaf_depth_split.
  unfold callee_body_depth, cached_depth, MaximumCall65Value.depth_value.
  now rewrite MaximumCall65Value.values_eq.
Qed.
Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumContext.depth leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
