From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall870Context MaximumCall870Leaf01Split MaximumCall870Leaf01Value.

Lemma leaf_lookup :
  List.nth_error MaximumCall870Context.leaves 1 = Some MaximumCall870Leaf01Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error MaximumCall870Context.leaves 1)). Qed.

Definition cached_values :=
  List.map MaximumCall870Context.depth (List.firstn 1 MaximumCall870Context.leaves) ++
  MaximumCall870Leaf01Value.value ::
  List.map MaximumCall870Context.depth (List.skipn 2 MaximumCall870Context.leaves).

Lemma cached_values_eq :
  List.map MaximumCall870Context.depth MaximumCall870Context.leaves = cached_values.
Proof.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall870Context.depth MaximumCall870Context.leaves 1 MaximumCall870Leaf01Split.leaf MaximumCall870Leaf01Value.value).
  - exact leaf_lookup.
  - exact MaximumCall870Leaf01Value.value_eq.
Qed.

Definition values := Eval vm_compute in cached_values.
Lemma values_eq : List.map MaximumCall870Context.depth MaximumCall870Context.leaves = values.
Proof.
  transitivity cached_values.
  - exact cached_values_eq.
  - vm_cast_no_check (eq_refl values).
Qed.

Definition depth_value := fold_right FastMaximum.join_depth (Some 0) values.
