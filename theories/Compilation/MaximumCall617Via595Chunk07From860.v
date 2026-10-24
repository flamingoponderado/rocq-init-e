From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall617Via595ContextFrom860 MaximumCall617Leaf59SplitFrom860 MaximumCall617Leaf59ValueFrom860 MaximumCall617Via595Chunk07PrefixFrom860 MaximumCall617Via595Chunk07SuffixFrom860.

Definition values :=
  MaximumCall617Via595Chunk07PrefixFrom860.values ++ MaximumCall617Leaf59ValueFrom860.value :: MaximumCall617Via595Chunk07SuffixFrom860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 7 MaximumCall617Via595ContextFrom860.leaves)
    3 = Some MaximumCall617Leaf59SplitFrom860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 7
    MaximumCall617Via595ContextFrom860.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall617Via595ContextFrom860.depth
    (MaximumListChunks.chunk_at 7 MaximumCall617Via595ContextFrom860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall617Via595Chunk07PrefixFrom860.values_eq.
  rewrite <- MaximumCall617Via595Chunk07SuffixFrom860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall617Via595ContextFrom860.depth (MaximumListChunks.chunk_at 7 MaximumCall617Via595ContextFrom860.leaves)
    3 MaximumCall617Leaf59SplitFrom860.leaf MaximumCall617Leaf59ValueFrom860.value).
  - exact leaf_lookup.
  - exact MaximumCall617Leaf59ValueFrom860.value_eq.
Qed.
