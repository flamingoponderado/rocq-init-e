From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Stdlib Require Import List.
From InitE.Compilation Require Import CallDepthLemma FastMaximum MaximumListChunks
  MaximumContext MaximumCall278Context MaximumCall278Leaf10Split
  MaximumCall68Value.

Definition cached_leaf_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall278Context.funs MaximumCall278Context.callee
    [MaximumCall278Context.callee] (sptree.size MaximumContext.funs)
    68 MaximumCall278Leaf10Split.ret_data
    MaximumCall278Leaf10Split.handler_data
    MaximumCall68Value.depth_value.

Lemma cached_leaf_depth_eq :
  MaximumCall278Context.depth MaximumCall278Leaf10Split.leaf = cached_leaf_depth.
Proof.
  rewrite MaximumCall278Leaf10Split.leaf_depth_compact.
  unfold cached_leaf_depth, MaximumCall278Leaf10Split.callee_body_depth,
    MaximumCall68Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall68Value.values_eq.
Qed.

Lemma leaf_lookup :
  List.nth_error MaximumCall278Context.leaves 10 =
  Some MaximumCall278Leaf10Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error MaximumCall278Context.leaves 10)). Qed.

Definition cached_values :=
  List.map MaximumCall278Context.depth
    (List.firstn 10 MaximumCall278Context.leaves) ++
  cached_leaf_depth ::
  List.map MaximumCall278Context.depth
    (List.skipn 11 MaximumCall278Context.leaves).

Lemma cached_values_eq :
  List.map MaximumCall278Context.depth MaximumCall278Context.leaves =
  cached_values.
Proof.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall278Context.depth MaximumCall278Context.leaves
    10 MaximumCall278Leaf10Split.leaf cached_leaf_depth).
  - exact leaf_lookup.
  - exact cached_leaf_depth_eq.
Qed.

Definition values := Eval vm_compute in cached_values.
Lemma values_eq :
  List.map MaximumCall278Context.depth MaximumCall278Context.leaves = values.
Proof.
  transitivity cached_values.
  - exact cached_values_eq.
  - vm_cast_no_check (eq_refl values).
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
