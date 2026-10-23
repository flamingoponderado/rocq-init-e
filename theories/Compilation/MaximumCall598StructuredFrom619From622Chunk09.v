From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall598StructuredFrom619From622Context MaximumCall598From619From622Leaf77Split MaximumCall598From619From622Leaf77Value MaximumCall598StructuredFrom619From622Chunk09Prefix MaximumCall598StructuredFrom619From622Chunk09Suffix.

Definition values :=
  MaximumCall598StructuredFrom619From622Chunk09Prefix.values ++ MaximumCall598From619From622Leaf77Value.value :: MaximumCall598StructuredFrom619From622Chunk09Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom619From622Context.leaves)
    5 = Some MaximumCall598From619From622Leaf77Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 9
    MaximumCall598StructuredFrom619From622Context.leaves) 5)). Qed.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom619From622Context.depth
    (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom619From622Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall598StructuredFrom619From622Chunk09Prefix.values_eq.
  rewrite <- MaximumCall598StructuredFrom619From622Chunk09Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall598StructuredFrom619From622Context.depth (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom619From622Context.leaves)
    5 MaximumCall598From619From622Leaf77Split.leaf MaximumCall598From619From622Leaf77Value.value).
  - exact leaf_lookup.
  - exact MaximumCall598From619From622Leaf77Value.value_eq.
Qed.
