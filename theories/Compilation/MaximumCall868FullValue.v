From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall868Context MaximumCall868Pieces MaximumCall868Prefix
  MaximumCall868Leaf06Split MaximumCall868Leaf06Value MaximumCall868Value.

Definition values :=
  MaximumCall868Prefix.values ++
  MaximumCall868Leaf06Value.value :: MaximumCall868Value.values.

Lemma leaf_lookup :
  List.nth_error MaximumCall868Context.leaves 6 =
    Some MaximumCall868Leaf06Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error MaximumCall868Context.leaves 6)). Qed.

Lemma values_eq :
  List.map MaximumCall868Context.depth MaximumCall868Context.leaves = values.
Proof.
  unfold values.
  rewrite <- MaximumCall868Prefix.values_eq.
  rewrite <- MaximumCall868Value.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall868Context.depth MaximumCall868Context.leaves 6
    MaximumCall868Leaf06Split.leaf MaximumCall868Leaf06Value.value).
  - exact leaf_lookup.
  - exact MaximumCall868Leaf06Value.value_eq.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
