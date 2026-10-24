From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall616Via617ContextFrom608 MaximumCall616From617Leaf124SplitFrom608 MaximumCall616From617Leaf124ValueFrom608 MaximumCall616Via617Chunk15PrefixFrom608 MaximumCall616Via617Chunk15SuffixFrom608.

Definition values :=
  MaximumCall616Via617Chunk15PrefixFrom608.values ++ MaximumCall616From617Leaf124ValueFrom608.value :: MaximumCall616Via617Chunk15SuffixFrom608.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 15 MaximumCall616Via617ContextFrom608.leaves)
    4 = Some MaximumCall616From617Leaf124SplitFrom608.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 15
    MaximumCall616Via617ContextFrom608.leaves) 4)). Qed.

Lemma values_eq :
  List.map MaximumCall616Via617ContextFrom608.depth
    (MaximumListChunks.chunk_at 15 MaximumCall616Via617ContextFrom608.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall616Via617Chunk15PrefixFrom608.values_eq.
  rewrite <- MaximumCall616Via617Chunk15SuffixFrom608.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall616Via617ContextFrom608.depth (MaximumListChunks.chunk_at 15 MaximumCall616Via617ContextFrom608.leaves)
    4 MaximumCall616From617Leaf124SplitFrom608.leaf MaximumCall616From617Leaf124ValueFrom608.value).
  - exact leaf_lookup.
  - exact MaximumCall616From617Leaf124ValueFrom608.value_eq.
Qed.
