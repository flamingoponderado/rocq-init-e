From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall595StructuredContextFrom860 MaximumCall595Leaf995SplitFrom860 MaximumCall595Leaf995ValueFrom860 MaximumCall595StructuredChunk124PrefixFrom860 MaximumCall595StructuredChunk124SuffixFrom860.

Definition values :=
  MaximumCall595StructuredChunk124PrefixFrom860.values ++ MaximumCall595Leaf995ValueFrom860.value :: MaximumCall595StructuredChunk124SuffixFrom860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 124 MaximumCall595StructuredContextFrom860.leaves)
    3 = Some MaximumCall595Leaf995SplitFrom860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 124
    MaximumCall595StructuredContextFrom860.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall595StructuredContextFrom860.depth
    (MaximumListChunks.chunk_at 124 MaximumCall595StructuredContextFrom860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall595StructuredChunk124PrefixFrom860.values_eq.
  rewrite <- MaximumCall595StructuredChunk124SuffixFrom860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall595StructuredContextFrom860.depth (MaximumListChunks.chunk_at 124 MaximumCall595StructuredContextFrom860.leaves)
    3 MaximumCall595Leaf995SplitFrom860.leaf MaximumCall595Leaf995ValueFrom860.value).
  - exact leaf_lookup.
  - exact MaximumCall595Leaf995ValueFrom860.value_eq.
Qed.
