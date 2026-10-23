From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall621Leaf148Context MaximumCall621Inner66Split MaximumCall621Inner66Value MaximumCall621Leaf148Chunk08Prefix MaximumCall621Leaf148Chunk08Suffix.

Definition values :=
  MaximumCall621Leaf148Chunk08Prefix.values ++ MaximumCall621Inner66Value.value :: MaximumCall621Leaf148Chunk08Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 8 MaximumCall621Leaf148Context.leaves)
    2 = Some MaximumCall621Inner66Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 8
    MaximumCall621Leaf148Context.leaves) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall621Leaf148Context.depth
    (MaximumListChunks.chunk_at 8 MaximumCall621Leaf148Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall621Leaf148Chunk08Prefix.values_eq.
  rewrite <- MaximumCall621Leaf148Chunk08Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall621Leaf148Context.depth (MaximumListChunks.chunk_at 8 MaximumCall621Leaf148Context.leaves)
    2 MaximumCall621Inner66Split.leaf MaximumCall621Inner66Value.value).
  - exact leaf_lookup.
  - exact MaximumCall621Inner66Value.value_eq.
Qed.
