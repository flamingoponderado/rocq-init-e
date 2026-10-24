From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall616Via618ContextFrom608From860 MaximumCall616From618Leaf124SplitFrom608From860 MaximumCall616From618Leaf124ValueFrom608From860 MaximumCall616Via618Chunk15PrefixFrom608From860 MaximumCall616Via618Chunk15SuffixFrom608From860.

Definition values :=
  MaximumCall616Via618Chunk15PrefixFrom608From860.values ++ MaximumCall616From618Leaf124ValueFrom608From860.value :: MaximumCall616Via618Chunk15SuffixFrom608From860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 15 MaximumCall616Via618ContextFrom608From860.leaves)
    4 = Some MaximumCall616From618Leaf124SplitFrom608From860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 15
    MaximumCall616Via618ContextFrom608From860.leaves) 4)). Qed.

Lemma values_eq :
  List.map MaximumCall616Via618ContextFrom608From860.depth
    (MaximumListChunks.chunk_at 15 MaximumCall616Via618ContextFrom608From860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall616Via618Chunk15PrefixFrom608From860.values_eq.
  rewrite <- MaximumCall616Via618Chunk15SuffixFrom608From860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall616Via618ContextFrom608From860.depth (MaximumListChunks.chunk_at 15 MaximumCall616Via618ContextFrom608From860.leaves)
    4 MaximumCall616From618Leaf124SplitFrom608From860.leaf MaximumCall616From618Leaf124ValueFrom608From860.value).
  - exact leaf_lookup.
  - exact MaximumCall616From618Leaf124ValueFrom608From860.value_eq.
Qed.
