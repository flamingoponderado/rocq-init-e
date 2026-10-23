From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall595StructuredContext MaximumCall595Leaf1043Split MaximumCall595Leaf1043Value MaximumCall595StructuredChunk130Prefix MaximumCall595StructuredChunk130Suffix.

Definition values :=
  MaximumCall595StructuredChunk130Prefix.values ++ MaximumCall595Leaf1043Value.value :: MaximumCall595StructuredChunk130Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 130 MaximumCall595StructuredContext.leaves)
    3 = Some MaximumCall595Leaf1043Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 130
    MaximumCall595StructuredContext.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall595StructuredContext.depth
    (MaximumListChunks.chunk_at 130 MaximumCall595StructuredContext.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall595StructuredChunk130Prefix.values_eq.
  rewrite <- MaximumCall595StructuredChunk130Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall595StructuredContext.depth (MaximumListChunks.chunk_at 130 MaximumCall595StructuredContext.leaves)
    3 MaximumCall595Leaf1043Split.leaf MaximumCall595Leaf1043Value.value).
  - exact leaf_lookup.
  - exact MaximumCall595Leaf1043Value.value_eq.
Qed.
