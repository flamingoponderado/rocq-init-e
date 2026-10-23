From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall619Via621Context MaximumCall619From621Leaf42Split MaximumCall619From621Leaf42Value MaximumCall619Via621Chunk05Prefix MaximumCall619Via621Chunk05Suffix.

Definition values :=
  MaximumCall619Via621Chunk05Prefix.values ++ MaximumCall619From621Leaf42Value.value :: MaximumCall619Via621Chunk05Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 5 MaximumCall619Via621Context.leaves)
    2 = Some MaximumCall619From621Leaf42Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 5
    MaximumCall619Via621Context.leaves) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall619Via621Context.depth
    (MaximumListChunks.chunk_at 5 MaximumCall619Via621Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall619Via621Chunk05Prefix.values_eq.
  rewrite <- MaximumCall619Via621Chunk05Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall619Via621Context.depth (MaximumListChunks.chunk_at 5 MaximumCall619Via621Context.leaves)
    2 MaximumCall619From621Leaf42Split.leaf MaximumCall619From621Leaf42Value.value).
  - exact leaf_lookup.
  - exact MaximumCall619From621Leaf42Value.value_eq.
Qed.
