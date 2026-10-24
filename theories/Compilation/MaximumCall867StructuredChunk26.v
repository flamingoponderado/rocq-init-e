From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall867StructuredContext MaximumCall867Leaf213Split MaximumCall867Leaf213Value MaximumCall867StructuredChunk26Prefix MaximumCall867StructuredChunk26Suffix.

Definition values :=
  MaximumCall867StructuredChunk26Prefix.values ++ MaximumCall867Leaf213Value.value :: MaximumCall867StructuredChunk26Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 26 MaximumCall867StructuredContext.leaves)
    5 = Some MaximumCall867Leaf213Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 26
    MaximumCall867StructuredContext.leaves) 5)). Qed.

Lemma values_eq :
  List.map MaximumCall867StructuredContext.depth
    (MaximumListChunks.chunk_at 26 MaximumCall867StructuredContext.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall867StructuredChunk26Prefix.values_eq.
  rewrite <- MaximumCall867StructuredChunk26Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall867StructuredContext.depth (MaximumListChunks.chunk_at 26 MaximumCall867StructuredContext.leaves)
    5 MaximumCall867Leaf213Split.leaf MaximumCall867Leaf213Value.value).
  - exact leaf_lookup.
  - exact MaximumCall867Leaf213Value.value_eq.
Qed.
