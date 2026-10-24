From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall867StructuredContext MaximumCall867Leaf169Split MaximumCall867Leaf169Value MaximumCall867StructuredChunk21Prefix MaximumCall867StructuredChunk21Suffix.

Definition values :=
  MaximumCall867StructuredChunk21Prefix.values ++ MaximumCall867Leaf169Value.value :: MaximumCall867StructuredChunk21Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 21 MaximumCall867StructuredContext.leaves)
    1 = Some MaximumCall867Leaf169Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 21
    MaximumCall867StructuredContext.leaves) 1)). Qed.

Lemma values_eq :
  List.map MaximumCall867StructuredContext.depth
    (MaximumListChunks.chunk_at 21 MaximumCall867StructuredContext.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall867StructuredChunk21Prefix.values_eq.
  rewrite <- MaximumCall867StructuredChunk21Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall867StructuredContext.depth (MaximumListChunks.chunk_at 21 MaximumCall867StructuredContext.leaves)
    1 MaximumCall867Leaf169Split.leaf MaximumCall867Leaf169Value.value).
  - exact leaf_lookup.
  - exact MaximumCall867Leaf169Value.value_eq.
Qed.
