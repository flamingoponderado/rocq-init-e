From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall603Via619From623ContextFrom608From860 MaximumCall603From619From623Leaf61SplitFrom608From860 MaximumCall603From619From623Leaf61ValueFrom608From860 MaximumCall603Via619From623Chunk07PrefixFrom608From860 MaximumCall603Via619From623Chunk07SuffixFrom608From860.

Definition values :=
  MaximumCall603Via619From623Chunk07PrefixFrom608From860.values ++ MaximumCall603From619From623Leaf61ValueFrom608From860.value :: MaximumCall603Via619From623Chunk07SuffixFrom608From860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 7 MaximumCall603Via619From623ContextFrom608From860.leaves)
    5 = Some MaximumCall603From619From623Leaf61SplitFrom608From860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 7
    MaximumCall603Via619From623ContextFrom608From860.leaves) 5)). Qed.

Lemma values_eq :
  List.map MaximumCall603Via619From623ContextFrom608From860.depth
    (MaximumListChunks.chunk_at 7 MaximumCall603Via619From623ContextFrom608From860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall603Via619From623Chunk07PrefixFrom608From860.values_eq.
  rewrite <- MaximumCall603Via619From623Chunk07SuffixFrom608From860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall603Via619From623ContextFrom608From860.depth (MaximumListChunks.chunk_at 7 MaximumCall603Via619From623ContextFrom608From860.leaves)
    5 MaximumCall603From619From623Leaf61SplitFrom608From860.leaf MaximumCall603From619From623Leaf61ValueFrom608From860.value).
  - exact leaf_lookup.
  - exact MaximumCall603From619From623Leaf61ValueFrom608From860.value_eq.
Qed.
