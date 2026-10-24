From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall861StructuredContext MaximumCall861Leaf25Split MaximumCall861Leaf25Value MaximumCall861StructuredChunk03Prefix MaximumCall861StructuredChunk03Suffix.

Definition values :=
  MaximumCall861StructuredChunk03Prefix.values ++ MaximumCall861Leaf25Value.value :: MaximumCall861StructuredChunk03Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 3 MaximumCall861StructuredContext.leaves)
    1 = Some MaximumCall861Leaf25Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 3
    MaximumCall861StructuredContext.leaves) 1)). Qed.

Lemma values_eq :
  List.map MaximumCall861StructuredContext.depth
    (MaximumListChunks.chunk_at 3 MaximumCall861StructuredContext.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall861StructuredChunk03Prefix.values_eq.
  rewrite <- MaximumCall861StructuredChunk03Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall861StructuredContext.depth (MaximumListChunks.chunk_at 3 MaximumCall861StructuredContext.leaves)
    1 MaximumCall861Leaf25Split.leaf MaximumCall861Leaf25Value.value).
  - exact leaf_lookup.
  - exact MaximumCall861Leaf25Value.value_eq.
Qed.
