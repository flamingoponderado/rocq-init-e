From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumContext MaximumRootLeaf339Callee MaximumRootLeaf339Value MaximumRootChunk42Prefix MaximumRootChunk42Suffix.

Definition values :=
  MaximumRootChunk42Prefix.values ++ MaximumRootLeaf339Value.value :: MaximumRootChunk42Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 42 MaximumContext.leaves)
    3 = Some MaximumRootLeaf339Callee.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 42
    MaximumContext.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumContext.depth
    (MaximumListChunks.chunk_at 42 MaximumContext.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumRootChunk42Prefix.values_eq.
  rewrite <- MaximumRootChunk42Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumContext.depth (MaximumListChunks.chunk_at 42 MaximumContext.leaves)
    3 MaximumRootLeaf339Callee.leaf MaximumRootLeaf339Value.value).
  - exact leaf_lookup.
  - exact MaximumRootLeaf339Value.value_eq.
Qed.
