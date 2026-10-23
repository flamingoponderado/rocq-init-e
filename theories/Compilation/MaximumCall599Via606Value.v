From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall599Via606Context MaximumCall599From606Leaf03Split MaximumCall599From606Leaf03Value.

Lemma leaf_lookup :
  List.nth_error MaximumCall599Via606Context.leaves 3 = Some MaximumCall599From606Leaf03Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error MaximumCall599Via606Context.leaves 3)). Qed.

Definition cached_values :=
  List.map MaximumCall599Via606Context.depth (List.firstn 3 MaximumCall599Via606Context.leaves) ++
  MaximumCall599From606Leaf03Value.value ::
  List.map MaximumCall599Via606Context.depth (List.skipn 4 MaximumCall599Via606Context.leaves).

Lemma cached_values_eq :
  List.map MaximumCall599Via606Context.depth MaximumCall599Via606Context.leaves = cached_values.
Proof.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall599Via606Context.depth MaximumCall599Via606Context.leaves 3 MaximumCall599From606Leaf03Split.leaf MaximumCall599From606Leaf03Value.value).
  - exact leaf_lookup.
  - exact MaximumCall599From606Leaf03Value.value_eq.
Qed.

Definition values := Eval vm_compute in cached_values.
Lemma values_eq : List.map MaximumCall599Via606Context.depth MaximumCall599Via606Context.leaves = values.
Proof.
  transitivity cached_values.
  - exact cached_values_eq.
  - vm_cast_no_check (eq_refl values).
Qed.

Definition depth_value := fold_right FastMaximum.join_depth (Some 0) values.
