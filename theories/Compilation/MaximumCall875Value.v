From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall875Context MaximumCall875Leaf01Split MaximumCall875Leaf01Value.

Lemma leaf_lookup :
  List.nth_error MaximumCall875Context.leaves 1 = Some MaximumCall875Leaf01Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error MaximumCall875Context.leaves 1)). Qed.

Definition cached_values :=
  List.map MaximumCall875Context.depth (List.firstn 1 MaximumCall875Context.leaves) ++
  MaximumCall875Leaf01Value.value ::
  List.map MaximumCall875Context.depth (List.skipn 2 MaximumCall875Context.leaves).

Lemma cached_values_eq :
  List.map MaximumCall875Context.depth MaximumCall875Context.leaves = cached_values.
Proof.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall875Context.depth MaximumCall875Context.leaves 1 MaximumCall875Leaf01Split.leaf MaximumCall875Leaf01Value.value).
  - exact leaf_lookup.
  - exact MaximumCall875Leaf01Value.value_eq.
Qed.

Definition values := Eval vm_compute in cached_values.
Lemma values_eq : List.map MaximumCall875Context.depth MaximumCall875Context.leaves = values.
Proof.
  transitivity cached_values.
  - exact cached_values_eq.
  - vm_cast_no_check (eq_refl values).
Qed.

Definition depth_value := fold_right FastMaximum.join_depth (Some 0) values.
