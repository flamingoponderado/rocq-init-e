From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall623Via595Context MaximumCall623Leaf131Split MaximumCall623Leaf131Value MaximumCall623Via595Chunk16Prefix MaximumCall623Via595Chunk16Suffix.

Definition values :=
  MaximumCall623Via595Chunk16Prefix.values ++ MaximumCall623Leaf131Value.value :: MaximumCall623Via595Chunk16Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 16 MaximumCall623Via595Context.leaves)
    3 = Some MaximumCall623Leaf131Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 16
    MaximumCall623Via595Context.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall623Via595Context.depth
    (MaximumListChunks.chunk_at 16 MaximumCall623Via595Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall623Via595Chunk16Prefix.values_eq.
  rewrite <- MaximumCall623Via595Chunk16Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall623Via595Context.depth (MaximumListChunks.chunk_at 16 MaximumCall623Via595Context.leaves)
    3 MaximumCall623Leaf131Split.leaf MaximumCall623Leaf131Value.value).
  - exact leaf_lookup.
  - exact MaximumCall623Leaf131Value.value_eq.
Qed.
