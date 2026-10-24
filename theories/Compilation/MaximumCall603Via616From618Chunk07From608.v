From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall603Via616From618ContextFrom608 MaximumCall603From616From618Leaf61SplitFrom608 MaximumCall603From616From618Leaf61ValueFrom608 MaximumCall603Via616From618Chunk07PrefixFrom608 MaximumCall603Via616From618Chunk07SuffixFrom608.

Definition values :=
  MaximumCall603Via616From618Chunk07PrefixFrom608.values ++ MaximumCall603From616From618Leaf61ValueFrom608.value :: MaximumCall603Via616From618Chunk07SuffixFrom608.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 7 MaximumCall603Via616From618ContextFrom608.leaves)
    5 = Some MaximumCall603From616From618Leaf61SplitFrom608.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 7
    MaximumCall603Via616From618ContextFrom608.leaves) 5)). Qed.

Lemma values_eq :
  List.map MaximumCall603Via616From618ContextFrom608.depth
    (MaximumListChunks.chunk_at 7 MaximumCall603Via616From618ContextFrom608.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall603Via616From618Chunk07PrefixFrom608.values_eq.
  rewrite <- MaximumCall603Via616From618Chunk07SuffixFrom608.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall603Via616From618ContextFrom608.depth (MaximumListChunks.chunk_at 7 MaximumCall603Via616From618ContextFrom608.leaves)
    5 MaximumCall603From616From618Leaf61SplitFrom608.leaf MaximumCall603From616From618Leaf61ValueFrom608.value).
  - exact leaf_lookup.
  - exact MaximumCall603From616From618Leaf61ValueFrom608.value_eq.
Qed.
