From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall623Via595ContextFrom860From861 MaximumCall623Leaf131SplitFrom860From861 MaximumCall623Leaf131ValueFrom860From861 MaximumCall623Via595Chunk16PrefixFrom860From861 MaximumCall623Via595Chunk16SuffixFrom860From861.

Definition values :=
  MaximumCall623Via595Chunk16PrefixFrom860From861.values ++ MaximumCall623Leaf131ValueFrom860From861.value :: MaximumCall623Via595Chunk16SuffixFrom860From861.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 16 MaximumCall623Via595ContextFrom860From861.leaves)
    3 = Some MaximumCall623Leaf131SplitFrom860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 16
    MaximumCall623Via595ContextFrom860From861.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall623Via595ContextFrom860From861.depth
    (MaximumListChunks.chunk_at 16 MaximumCall623Via595ContextFrom860From861.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall623Via595Chunk16PrefixFrom860From861.values_eq.
  rewrite <- MaximumCall623Via595Chunk16SuffixFrom860From861.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall623Via595ContextFrom860From861.depth (MaximumListChunks.chunk_at 16 MaximumCall623Via595ContextFrom860From861.leaves)
    3 MaximumCall623Leaf131SplitFrom860From861.leaf MaximumCall623Leaf131ValueFrom860From861.value).
  - exact leaf_lookup.
  - exact MaximumCall623Leaf131ValueFrom860From861.value_eq.
Qed.
