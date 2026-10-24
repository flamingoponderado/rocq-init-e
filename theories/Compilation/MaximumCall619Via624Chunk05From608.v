From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall619Via624ContextFrom608 MaximumCall619From624Leaf42SplitFrom608 MaximumCall619From624Leaf42ValueFrom608 MaximumCall619Via624Chunk05PrefixFrom608 MaximumCall619Via624Chunk05SuffixFrom608.

Definition values :=
  MaximumCall619Via624Chunk05PrefixFrom608.values ++ MaximumCall619From624Leaf42ValueFrom608.value :: MaximumCall619Via624Chunk05SuffixFrom608.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 5 MaximumCall619Via624ContextFrom608.leaves)
    2 = Some MaximumCall619From624Leaf42SplitFrom608.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 5
    MaximumCall619Via624ContextFrom608.leaves) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall619Via624ContextFrom608.depth
    (MaximumListChunks.chunk_at 5 MaximumCall619Via624ContextFrom608.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall619Via624Chunk05PrefixFrom608.values_eq.
  rewrite <- MaximumCall619Via624Chunk05SuffixFrom608.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall619Via624ContextFrom608.depth (MaximumListChunks.chunk_at 5 MaximumCall619Via624ContextFrom608.leaves)
    2 MaximumCall619From624Leaf42SplitFrom608.leaf MaximumCall619From624Leaf42ValueFrom608.value).
  - exact leaf_lookup.
  - exact MaximumCall619From624Leaf42ValueFrom608.value_eq.
Qed.
