From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall619Via623ContextFrom860 MaximumCall619From623Leaf42SplitFrom860 MaximumCall619From623Leaf42ValueFrom860 MaximumCall619Via623Chunk05PrefixFrom860 MaximumCall619Via623Chunk05SuffixFrom860.

Definition values :=
  MaximumCall619Via623Chunk05PrefixFrom860.values ++ MaximumCall619From623Leaf42ValueFrom860.value :: MaximumCall619Via623Chunk05SuffixFrom860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 5 MaximumCall619Via623ContextFrom860.leaves)
    2 = Some MaximumCall619From623Leaf42SplitFrom860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 5
    MaximumCall619Via623ContextFrom860.leaves) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall619Via623ContextFrom860.depth
    (MaximumListChunks.chunk_at 5 MaximumCall619Via623ContextFrom860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall619Via623Chunk05PrefixFrom860.values_eq.
  rewrite <- MaximumCall619Via623Chunk05SuffixFrom860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall619Via623ContextFrom860.depth (MaximumListChunks.chunk_at 5 MaximumCall619Via623ContextFrom860.leaves)
    2 MaximumCall619From623Leaf42SplitFrom860.leaf MaximumCall619From623Leaf42ValueFrom860.value).
  - exact leaf_lookup.
  - exact MaximumCall619From623Leaf42ValueFrom860.value_eq.
Qed.
