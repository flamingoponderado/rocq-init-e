From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall619Via624Context MaximumCall619From624Leaf42Split MaximumCall619From624Leaf42Value MaximumCall619Via624Chunk05Prefix MaximumCall619Via624Chunk05Suffix.

Definition values :=
  MaximumCall619Via624Chunk05Prefix.values ++ MaximumCall619From624Leaf42Value.value :: MaximumCall619Via624Chunk05Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 5 MaximumCall619Via624Context.leaves)
    2 = Some MaximumCall619From624Leaf42Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 5
    MaximumCall619Via624Context.leaves) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall619Via624Context.depth
    (MaximumListChunks.chunk_at 5 MaximumCall619Via624Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall619Via624Chunk05Prefix.values_eq.
  rewrite <- MaximumCall619Via624Chunk05Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall619Via624Context.depth (MaximumListChunks.chunk_at 5 MaximumCall619Via624Context.leaves)
    2 MaximumCall619From624Leaf42Split.leaf MaximumCall619From624Leaf42Value.value).
  - exact leaf_lookup.
  - exact MaximumCall619From624Leaf42Value.value_eq.
Qed.
