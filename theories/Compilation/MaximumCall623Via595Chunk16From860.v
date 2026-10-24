From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall623Via595ContextFrom860 MaximumCall623Leaf131SplitFrom860 MaximumCall623Leaf131ValueFrom860 MaximumCall623Via595Chunk16PrefixFrom860 MaximumCall623Via595Chunk16SuffixFrom860.

Definition values :=
  MaximumCall623Via595Chunk16PrefixFrom860.values ++ MaximumCall623Leaf131ValueFrom860.value :: MaximumCall623Via595Chunk16SuffixFrom860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 16 MaximumCall623Via595ContextFrom860.leaves)
    3 = Some MaximumCall623Leaf131SplitFrom860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 16
    MaximumCall623Via595ContextFrom860.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall623Via595ContextFrom860.depth
    (MaximumListChunks.chunk_at 16 MaximumCall623Via595ContextFrom860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall623Via595Chunk16PrefixFrom860.values_eq.
  rewrite <- MaximumCall623Via595Chunk16SuffixFrom860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall623Via595ContextFrom860.depth (MaximumListChunks.chunk_at 16 MaximumCall623Via595ContextFrom860.leaves)
    3 MaximumCall623Leaf131SplitFrom860.leaf MaximumCall623Leaf131ValueFrom860.value).
  - exact leaf_lookup.
  - exact MaximumCall623Leaf131ValueFrom860.value_eq.
Qed.
