From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall621Via595Context MaximumCall621Leaf148Context MaximumCall621Leaf148OuterValue MaximumCall621Via595Chunk18Prefix MaximumCall621Via595Chunk18Suffix.

Definition values :=
  MaximumCall621Via595Chunk18Prefix.values ++ MaximumCall621Leaf148OuterValue.value :: MaximumCall621Via595Chunk18Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 18 MaximumCall621Via595Context.leaves)
    4 = Some MaximumCall621Leaf148Context.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 18
    MaximumCall621Via595Context.leaves) 4)). Qed.

Lemma values_eq :
  List.map MaximumCall621Via595Context.depth
    (MaximumListChunks.chunk_at 18 MaximumCall621Via595Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall621Via595Chunk18Prefix.values_eq.
  rewrite <- MaximumCall621Via595Chunk18Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall621Via595Context.depth (MaximumListChunks.chunk_at 18 MaximumCall621Via595Context.leaves)
    4 MaximumCall621Leaf148Context.leaf MaximumCall621Leaf148OuterValue.value).
  - exact leaf_lookup.
  - exact MaximumCall621Leaf148OuterValue.value_eq.
Qed.
