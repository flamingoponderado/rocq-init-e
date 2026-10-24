From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall616Via617ContextFrom860 MaximumCall616From617Leaf131SplitFrom860 MaximumCall616From617Leaf131ValueFrom860 MaximumCall616Via617Chunk16PrefixFrom860 MaximumCall616Via617Chunk16SuffixFrom860.

Definition values :=
  MaximumCall616Via617Chunk16PrefixFrom860.values ++ MaximumCall616From617Leaf131ValueFrom860.value :: MaximumCall616Via617Chunk16SuffixFrom860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 16 MaximumCall616Via617ContextFrom860.leaves)
    3 = Some MaximumCall616From617Leaf131SplitFrom860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 16
    MaximumCall616Via617ContextFrom860.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall616Via617ContextFrom860.depth
    (MaximumListChunks.chunk_at 16 MaximumCall616Via617ContextFrom860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall616Via617Chunk16PrefixFrom860.values_eq.
  rewrite <- MaximumCall616Via617Chunk16SuffixFrom860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall616Via617ContextFrom860.depth (MaximumListChunks.chunk_at 16 MaximumCall616Via617ContextFrom860.leaves)
    3 MaximumCall616From617Leaf131SplitFrom860.leaf MaximumCall616From617Leaf131ValueFrom860.value).
  - exact leaf_lookup.
  - exact MaximumCall616From617Leaf131ValueFrom860.value_eq.
Qed.
