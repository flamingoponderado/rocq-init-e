From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall595StructuredContext MaximumCall595Leaf1055Split MaximumCall595Leaf1055Value MaximumCall595StructuredChunk131Prefix MaximumCall595StructuredChunk131Suffix.

Definition values :=
  MaximumCall595StructuredChunk131Prefix.values ++ MaximumCall595Leaf1055Value.value :: MaximumCall595StructuredChunk131Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 131 MaximumCall595StructuredContext.leaves)
    7 = Some MaximumCall595Leaf1055Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 131
    MaximumCall595StructuredContext.leaves) 7)). Qed.

Lemma values_eq :
  List.map MaximumCall595StructuredContext.depth
    (MaximumListChunks.chunk_at 131 MaximumCall595StructuredContext.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall595StructuredChunk131Prefix.values_eq.
  rewrite <- MaximumCall595StructuredChunk131Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall595StructuredContext.depth (MaximumListChunks.chunk_at 131 MaximumCall595StructuredContext.leaves)
    7 MaximumCall595Leaf1055Split.leaf MaximumCall595Leaf1055Value.value).
  - exact leaf_lookup.
  - exact MaximumCall595Leaf1055Value.value_eq.
Qed.
