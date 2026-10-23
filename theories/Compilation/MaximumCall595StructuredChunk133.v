From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall595StructuredContext MaximumCall595Leaf1067Split MaximumCall595Leaf1067Value MaximumCall595StructuredChunk133Prefix MaximumCall595StructuredChunk133Suffix.

Definition values :=
  MaximumCall595StructuredChunk133Prefix.values ++ MaximumCall595Leaf1067Value.value :: MaximumCall595StructuredChunk133Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 133 MaximumCall595StructuredContext.leaves)
    3 = Some MaximumCall595Leaf1067Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 133
    MaximumCall595StructuredContext.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall595StructuredContext.depth
    (MaximumListChunks.chunk_at 133 MaximumCall595StructuredContext.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall595StructuredChunk133Prefix.values_eq.
  rewrite <- MaximumCall595StructuredChunk133Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall595StructuredContext.depth (MaximumListChunks.chunk_at 133 MaximumCall595StructuredContext.leaves)
    3 MaximumCall595Leaf1067Split.leaf MaximumCall595Leaf1067Value.value).
  - exact leaf_lookup.
  - exact MaximumCall595Leaf1067Value.value_eq.
Qed.
