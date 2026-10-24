From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall621Leaf148ContextFrom608 MaximumCall621Inner66SplitFrom608 MaximumCall621Inner66ValueFrom608 MaximumCall621Leaf148Chunk08PrefixFrom608 MaximumCall621Leaf148Chunk08SuffixFrom608.

Definition values :=
  MaximumCall621Leaf148Chunk08PrefixFrom608.values ++ MaximumCall621Inner66ValueFrom608.value :: MaximumCall621Leaf148Chunk08SuffixFrom608.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 8 MaximumCall621Leaf148ContextFrom608.leaves)
    2 = Some MaximumCall621Inner66SplitFrom608.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 8
    MaximumCall621Leaf148ContextFrom608.leaves) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall621Leaf148ContextFrom608.depth
    (MaximumListChunks.chunk_at 8 MaximumCall621Leaf148ContextFrom608.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall621Leaf148Chunk08PrefixFrom608.values_eq.
  rewrite <- MaximumCall621Leaf148Chunk08SuffixFrom608.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall621Leaf148ContextFrom608.depth (MaximumListChunks.chunk_at 8 MaximumCall621Leaf148ContextFrom608.leaves)
    2 MaximumCall621Inner66SplitFrom608.leaf MaximumCall621Inner66ValueFrom608.value).
  - exact leaf_lookup.
  - exact MaximumCall621Inner66ValueFrom608.value_eq.
Qed.
