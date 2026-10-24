From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall616Via617ContextFrom860From861 MaximumCall616From617Leaf131SplitFrom860From861 MaximumCall616From617Leaf131ValueFrom860From861 MaximumCall616Via617Chunk16PrefixFrom860From861 MaximumCall616Via617Chunk16SuffixFrom860From861.

Definition values :=
  MaximumCall616Via617Chunk16PrefixFrom860From861.values ++ MaximumCall616From617Leaf131ValueFrom860From861.value :: MaximumCall616Via617Chunk16SuffixFrom860From861.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 16 MaximumCall616Via617ContextFrom860From861.leaves)
    3 = Some MaximumCall616From617Leaf131SplitFrom860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 16
    MaximumCall616Via617ContextFrom860From861.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall616Via617ContextFrom860From861.depth
    (MaximumListChunks.chunk_at 16 MaximumCall616Via617ContextFrom860From861.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall616Via617Chunk16PrefixFrom860From861.values_eq.
  rewrite <- MaximumCall616Via617Chunk16SuffixFrom860From861.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall616Via617ContextFrom860From861.depth (MaximumListChunks.chunk_at 16 MaximumCall616Via617ContextFrom860From861.leaves)
    3 MaximumCall616From617Leaf131SplitFrom860From861.leaf MaximumCall616From617Leaf131ValueFrom860From861.value).
  - exact leaf_lookup.
  - exact MaximumCall616From617Leaf131ValueFrom860From861.value_eq.
Qed.
