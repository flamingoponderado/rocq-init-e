From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall621Leaf148ContextFrom860 MaximumCall621Inner66SplitFrom860 MaximumCall621Inner66ValueFrom860 MaximumCall621Leaf148Chunk08PrefixFrom860 MaximumCall621Leaf148Chunk08SuffixFrom860.

Definition values :=
  MaximumCall621Leaf148Chunk08PrefixFrom860.values ++ MaximumCall621Inner66ValueFrom860.value :: MaximumCall621Leaf148Chunk08SuffixFrom860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 8 MaximumCall621Leaf148ContextFrom860.leaves)
    2 = Some MaximumCall621Inner66SplitFrom860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 8
    MaximumCall621Leaf148ContextFrom860.leaves) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall621Leaf148ContextFrom860.depth
    (MaximumListChunks.chunk_at 8 MaximumCall621Leaf148ContextFrom860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall621Leaf148Chunk08PrefixFrom860.values_eq.
  rewrite <- MaximumCall621Leaf148Chunk08SuffixFrom860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall621Leaf148ContextFrom860.depth (MaximumListChunks.chunk_at 8 MaximumCall621Leaf148ContextFrom860.leaves)
    2 MaximumCall621Inner66SplitFrom860.leaf MaximumCall621Inner66ValueFrom860.value).
  - exact leaf_lookup.
  - exact MaximumCall621Inner66ValueFrom860.value_eq.
Qed.
