From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall603Via616From618Context MaximumCall603From616From618Leaf61Split MaximumCall603From616From618Leaf61Value MaximumCall603Via616From618Chunk07Prefix MaximumCall603Via616From618Chunk07Suffix.

Definition values :=
  MaximumCall603Via616From618Chunk07Prefix.values ++ MaximumCall603From616From618Leaf61Value.value :: MaximumCall603Via616From618Chunk07Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 7 MaximumCall603Via616From618Context.leaves)
    5 = Some MaximumCall603From616From618Leaf61Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 7
    MaximumCall603Via616From618Context.leaves) 5)). Qed.

Lemma values_eq :
  List.map MaximumCall603Via616From618Context.depth
    (MaximumListChunks.chunk_at 7 MaximumCall603Via616From618Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall603Via616From618Chunk07Prefix.values_eq.
  rewrite <- MaximumCall603Via616From618Chunk07Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall603Via616From618Context.depth (MaximumListChunks.chunk_at 7 MaximumCall603Via616From618Context.leaves)
    5 MaximumCall603From616From618Leaf61Split.leaf MaximumCall603From616From618Leaf61Value.value).
  - exact leaf_lookup.
  - exact MaximumCall603From616From618Leaf61Value.value_eq.
Qed.
