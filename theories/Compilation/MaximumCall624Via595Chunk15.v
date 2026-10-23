From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall624Via595Context MaximumCall624Leaf125Split MaximumCall624Leaf125Value MaximumCall624Via595Chunk15Prefix MaximumCall624Via595Chunk15Suffix.

Definition values :=
  MaximumCall624Via595Chunk15Prefix.values ++ MaximumCall624Leaf125Value.value :: MaximumCall624Via595Chunk15Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 15 MaximumCall624Via595Context.leaves)
    5 = Some MaximumCall624Leaf125Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 15
    MaximumCall624Via595Context.leaves) 5)). Qed.

Lemma values_eq :
  List.map MaximumCall624Via595Context.depth
    (MaximumListChunks.chunk_at 15 MaximumCall624Via595Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall624Via595Chunk15Prefix.values_eq.
  rewrite <- MaximumCall624Via595Chunk15Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall624Via595Context.depth (MaximumListChunks.chunk_at 15 MaximumCall624Via595Context.leaves)
    5 MaximumCall624Leaf125Split.leaf MaximumCall624Leaf125Value.value).
  - exact leaf_lookup.
  - exact MaximumCall624Leaf125Value.value_eq.
Qed.
