From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall595StructuredContext MaximumCall595Leaf1019Split MaximumCall595Leaf1019Value MaximumCall595StructuredChunk127Prefix MaximumCall595StructuredChunk127Suffix.

Definition values :=
  MaximumCall595StructuredChunk127Prefix.values ++ MaximumCall595Leaf1019Value.value :: MaximumCall595StructuredChunk127Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 127 MaximumCall595StructuredContext.leaves)
    3 = Some MaximumCall595Leaf1019Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 127
    MaximumCall595StructuredContext.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall595StructuredContext.depth
    (MaximumListChunks.chunk_at 127 MaximumCall595StructuredContext.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall595StructuredChunk127Prefix.values_eq.
  rewrite <- MaximumCall595StructuredChunk127Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall595StructuredContext.depth (MaximumListChunks.chunk_at 127 MaximumCall595StructuredContext.leaves)
    3 MaximumCall595Leaf1019Split.leaf MaximumCall595Leaf1019Value.value).
  - exact leaf_lookup.
  - exact MaximumCall595Leaf1019Value.value_eq.
Qed.
