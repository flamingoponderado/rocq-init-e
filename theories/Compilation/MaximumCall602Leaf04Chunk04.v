From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall602Leaf04Context MaximumCall602Inner35Split MaximumCall602Inner35Value MaximumCall602Leaf04Chunk04Prefix MaximumCall602Leaf04Chunk04Suffix.

Definition values :=
  MaximumCall602Leaf04Chunk04Prefix.values ++ MaximumCall602Inner35Value.value :: MaximumCall602Leaf04Chunk04Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 4 MaximumCall602Leaf04Context.leaves)
    3 = Some MaximumCall602Inner35Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 4
    MaximumCall602Leaf04Context.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall602Leaf04Context.depth
    (MaximumListChunks.chunk_at 4 MaximumCall602Leaf04Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall602Leaf04Chunk04Prefix.values_eq.
  rewrite <- MaximumCall602Leaf04Chunk04Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall602Leaf04Context.depth (MaximumListChunks.chunk_at 4 MaximumCall602Leaf04Context.leaves)
    3 MaximumCall602Inner35Split.leaf MaximumCall602Inner35Value.value).
  - exact leaf_lookup.
  - exact MaximumCall602Inner35Value.value_eq.
Qed.
