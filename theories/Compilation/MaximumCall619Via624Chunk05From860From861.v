From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall619Via624ContextFrom860From861 MaximumCall619From624Leaf42SplitFrom860From861 MaximumCall619From624Leaf42ValueFrom860From861 MaximumCall619Via624Chunk05PrefixFrom860From861 MaximumCall619Via624Chunk05SuffixFrom860From861.

Definition values :=
  MaximumCall619Via624Chunk05PrefixFrom860From861.values ++ MaximumCall619From624Leaf42ValueFrom860From861.value :: MaximumCall619Via624Chunk05SuffixFrom860From861.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 5 MaximumCall619Via624ContextFrom860From861.leaves)
    2 = Some MaximumCall619From624Leaf42SplitFrom860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 5
    MaximumCall619Via624ContextFrom860From861.leaves) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall619Via624ContextFrom860From861.depth
    (MaximumListChunks.chunk_at 5 MaximumCall619Via624ContextFrom860From861.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall619Via624Chunk05PrefixFrom860From861.values_eq.
  rewrite <- MaximumCall619Via624Chunk05SuffixFrom860From861.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall619Via624ContextFrom860From861.depth (MaximumListChunks.chunk_at 5 MaximumCall619Via624ContextFrom860From861.leaves)
    2 MaximumCall619From624Leaf42SplitFrom860From861.leaf MaximumCall619From624Leaf42ValueFrom860From861.value).
  - exact leaf_lookup.
  - exact MaximumCall619From624Leaf42ValueFrom860From861.value_eq.
Qed.
