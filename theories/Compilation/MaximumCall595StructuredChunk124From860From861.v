From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall595StructuredContextFrom860From861 MaximumCall595Leaf995SplitFrom860From861 MaximumCall595Leaf995ValueFrom860From861 MaximumCall595StructuredChunk124PrefixFrom860From861 MaximumCall595StructuredChunk124SuffixFrom860From861.

Definition values :=
  MaximumCall595StructuredChunk124PrefixFrom860From861.values ++ MaximumCall595Leaf995ValueFrom860From861.value :: MaximumCall595StructuredChunk124SuffixFrom860From861.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 124 MaximumCall595StructuredContextFrom860From861.leaves)
    3 = Some MaximumCall595Leaf995SplitFrom860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 124
    MaximumCall595StructuredContextFrom860From861.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall595StructuredContextFrom860From861.depth
    (MaximumListChunks.chunk_at 124 MaximumCall595StructuredContextFrom860From861.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall595StructuredChunk124PrefixFrom860From861.values_eq.
  rewrite <- MaximumCall595StructuredChunk124SuffixFrom860From861.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall595StructuredContextFrom860From861.depth (MaximumListChunks.chunk_at 124 MaximumCall595StructuredContextFrom860From861.leaves)
    3 MaximumCall595Leaf995SplitFrom860From861.leaf MaximumCall595Leaf995ValueFrom860From861.value).
  - exact leaf_lookup.
  - exact MaximumCall595Leaf995ValueFrom860From861.value_eq.
Qed.
