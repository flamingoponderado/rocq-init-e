From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall867StructuredContext MaximumCall867Leaf191Split MaximumCall867Leaf191Value MaximumCall867StructuredChunk23Prefix MaximumCall867StructuredChunk23Suffix.

Definition values :=
  MaximumCall867StructuredChunk23Prefix.values ++ MaximumCall867Leaf191Value.value :: MaximumCall867StructuredChunk23Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 23 MaximumCall867StructuredContext.leaves)
    7 = Some MaximumCall867Leaf191Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 23
    MaximumCall867StructuredContext.leaves) 7)). Qed.

Lemma values_eq :
  List.map MaximumCall867StructuredContext.depth
    (MaximumListChunks.chunk_at 23 MaximumCall867StructuredContext.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall867StructuredChunk23Prefix.values_eq.
  rewrite <- MaximumCall867StructuredChunk23Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall867StructuredContext.depth (MaximumListChunks.chunk_at 23 MaximumCall867StructuredContext.leaves)
    7 MaximumCall867Leaf191Split.leaf MaximumCall867Leaf191Value.value).
  - exact leaf_lookup.
  - exact MaximumCall867Leaf191Value.value_eq.
Qed.
