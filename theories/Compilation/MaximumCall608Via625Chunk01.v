From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall608Via625Context MaximumCall608Leaf15Split MaximumCall608Leaf15Value MaximumCall608Via625Chunk01Prefix MaximumCall608Via625Chunk01Suffix.

Definition values :=
  MaximumCall608Via625Chunk01Prefix.values ++ MaximumCall608Leaf15Value.value :: MaximumCall608Via625Chunk01Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 1 MaximumCall608Via625Context.leaves)
    7 = Some MaximumCall608Leaf15Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 1
    MaximumCall608Via625Context.leaves) 7)). Qed.

Lemma values_eq :
  List.map MaximumCall608Via625Context.depth
    (MaximumListChunks.chunk_at 1 MaximumCall608Via625Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall608Via625Chunk01Prefix.values_eq.
  rewrite <- MaximumCall608Via625Chunk01Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall608Via625Context.depth (MaximumListChunks.chunk_at 1 MaximumCall608Via625Context.leaves)
    7 MaximumCall608Leaf15Split.leaf MaximumCall608Leaf15Value.value).
  - exact leaf_lookup.
  - exact MaximumCall608Leaf15Value.value_eq.
Qed.
