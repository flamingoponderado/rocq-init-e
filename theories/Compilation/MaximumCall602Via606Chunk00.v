From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall602Via606Context MaximumCall602Leaf04Alias MaximumCall602Leaf04OuterValue MaximumCall602Via606Chunk00Prefix MaximumCall602Via606Chunk00Suffix.

Definition values :=
  MaximumCall602Via606Chunk00Prefix.values ++ MaximumCall602Leaf04OuterValue.value :: MaximumCall602Via606Chunk00Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 0 MaximumCall602Via606Context.leaves)
    4 = Some MaximumCall602Leaf04Alias.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 0
    MaximumCall602Via606Context.leaves) 4)). Qed.

Lemma values_eq :
  List.map MaximumCall602Via606Context.depth
    (MaximumListChunks.chunk_at 0 MaximumCall602Via606Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall602Via606Chunk00Prefix.values_eq.
  rewrite <- MaximumCall602Via606Chunk00Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall602Via606Context.depth (MaximumListChunks.chunk_at 0 MaximumCall602Via606Context.leaves)
    4 MaximumCall602Leaf04Alias.leaf MaximumCall602Leaf04OuterValue.value).
  - exact leaf_lookup.
  - exact MaximumCall602Leaf04OuterValue.value_eq.
Qed.
