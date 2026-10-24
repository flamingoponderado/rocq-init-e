From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall599Via603From619From621ContextFrom608 MaximumCall599From619From621Leaf03SplitFrom608 MaximumCall599From619From621Leaf03ValueFrom608.

Lemma leaf_lookup :
  List.nth_error MaximumCall599Via603From619From621ContextFrom608.leaves 3 = Some MaximumCall599From619From621Leaf03SplitFrom608.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error MaximumCall599Via603From619From621ContextFrom608.leaves 3)). Qed.

Definition cached_values :=
  List.map MaximumCall599Via603From619From621ContextFrom608.depth (List.firstn 3 MaximumCall599Via603From619From621ContextFrom608.leaves) ++
  MaximumCall599From619From621Leaf03ValueFrom608.value ::
  List.map MaximumCall599Via603From619From621ContextFrom608.depth (List.skipn 4 MaximumCall599Via603From619From621ContextFrom608.leaves).

Lemma cached_values_eq :
  List.map MaximumCall599Via603From619From621ContextFrom608.depth MaximumCall599Via603From619From621ContextFrom608.leaves = cached_values.
Proof.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall599Via603From619From621ContextFrom608.depth MaximumCall599Via603From619From621ContextFrom608.leaves 3 MaximumCall599From619From621Leaf03SplitFrom608.leaf MaximumCall599From619From621Leaf03ValueFrom608.value).
  - exact leaf_lookup.
  - exact MaximumCall599From619From621Leaf03ValueFrom608.value_eq.
Qed.

Definition values := Eval vm_compute in cached_values.
Lemma values_eq : List.map MaximumCall599Via603From619From621ContextFrom608.depth MaximumCall599Via603From619From621ContextFrom608.leaves = values.
Proof.
  transitivity cached_values.
  - exact cached_values_eq.
  - vm_cast_no_check (eq_refl values).
Qed.

Definition depth_value := fold_right FastMaximum.join_depth (Some 0) values.
