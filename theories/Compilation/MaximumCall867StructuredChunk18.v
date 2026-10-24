From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall867StructuredContext MaximumCall867Leaf147Split MaximumCall867Leaf147Value MaximumCall867StructuredChunk18Prefix MaximumCall867StructuredChunk18Suffix.

Definition values :=
  MaximumCall867StructuredChunk18Prefix.values ++ MaximumCall867Leaf147Value.value :: MaximumCall867StructuredChunk18Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 18 MaximumCall867StructuredContext.leaves)
    3 = Some MaximumCall867Leaf147Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 18
    MaximumCall867StructuredContext.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall867StructuredContext.depth
    (MaximumListChunks.chunk_at 18 MaximumCall867StructuredContext.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall867StructuredChunk18Prefix.values_eq.
  rewrite <- MaximumCall867StructuredChunk18Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall867StructuredContext.depth (MaximumListChunks.chunk_at 18 MaximumCall867StructuredContext.leaves)
    3 MaximumCall867Leaf147Split.leaf MaximumCall867Leaf147Value.value).
  - exact leaf_lookup.
  - exact MaximumCall867Leaf147Value.value_eq.
Qed.
