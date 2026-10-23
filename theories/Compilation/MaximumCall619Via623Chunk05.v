From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall619Via623Context MaximumCall619From623Leaf42Split MaximumCall619From623Leaf42Value MaximumCall619Via623Chunk05Prefix MaximumCall619Via623Chunk05Suffix.

Definition values :=
  MaximumCall619Via623Chunk05Prefix.values ++ MaximumCall619From623Leaf42Value.value :: MaximumCall619Via623Chunk05Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 5 MaximumCall619Via623Context.leaves)
    2 = Some MaximumCall619From623Leaf42Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 5
    MaximumCall619Via623Context.leaves) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall619Via623Context.depth
    (MaximumListChunks.chunk_at 5 MaximumCall619Via623Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall619Via623Chunk05Prefix.values_eq.
  rewrite <- MaximumCall619Via623Chunk05Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall619Via623Context.depth (MaximumListChunks.chunk_at 5 MaximumCall619Via623Context.leaves)
    2 MaximumCall619From623Leaf42Split.leaf MaximumCall619From623Leaf42Value.value).
  - exact leaf_lookup.
  - exact MaximumCall619From623Leaf42Value.value_eq.
Qed.
