From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall877Context MaximumCall877Leaf03Split MaximumCall877Leaf03Value.

Lemma leaf_lookup :
  List.nth_error MaximumCall877Context.leaves 3 = Some MaximumCall877Leaf03Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error MaximumCall877Context.leaves 3)). Qed.

Definition cached_values :=
  List.map MaximumCall877Context.depth (List.firstn 3 MaximumCall877Context.leaves) ++
  MaximumCall877Leaf03Value.value ::
  List.map MaximumCall877Context.depth (List.skipn 4 MaximumCall877Context.leaves).

Lemma cached_values_eq :
  List.map MaximumCall877Context.depth MaximumCall877Context.leaves = cached_values.
Proof.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall877Context.depth MaximumCall877Context.leaves 3 MaximumCall877Leaf03Split.leaf MaximumCall877Leaf03Value.value).
  - exact leaf_lookup.
  - exact MaximumCall877Leaf03Value.value_eq.
Qed.

Definition values := Eval vm_compute in cached_values.
Lemma values_eq : List.map MaximumCall877Context.depth MaximumCall877Context.leaves = values.
Proof.
  transitivity cached_values.
  - exact cached_values_eq.
  - vm_cast_no_check (eq_refl values).
Qed.

Definition depth_value := fold_right FastMaximum.join_depth (Some 0) values.
