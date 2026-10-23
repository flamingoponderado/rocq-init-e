From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall595StructuredContext MaximumCall595Leaf995Split MaximumCall595Leaf995Value MaximumCall595StructuredChunk124Prefix MaximumCall595StructuredChunk124Suffix.

Definition values :=
  MaximumCall595StructuredChunk124Prefix.values ++ MaximumCall595Leaf995Value.value :: MaximumCall595StructuredChunk124Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 124 MaximumCall595StructuredContext.leaves)
    3 = Some MaximumCall595Leaf995Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 124
    MaximumCall595StructuredContext.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall595StructuredContext.depth
    (MaximumListChunks.chunk_at 124 MaximumCall595StructuredContext.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall595StructuredChunk124Prefix.values_eq.
  rewrite <- MaximumCall595StructuredChunk124Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall595StructuredContext.depth (MaximumListChunks.chunk_at 124 MaximumCall595StructuredContext.leaves)
    3 MaximumCall595Leaf995Split.leaf MaximumCall595Leaf995Value.value).
  - exact leaf_lookup.
  - exact MaximumCall595Leaf995Value.value_eq.
Qed.
