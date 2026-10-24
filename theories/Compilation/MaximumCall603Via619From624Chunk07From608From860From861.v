From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall603Via619From624ContextFrom608From860From861 MaximumCall603From619From624Leaf61SplitFrom608From860From861 MaximumCall603From619From624Leaf61ValueFrom608From860From861 MaximumCall603Via619From624Chunk07PrefixFrom608From860From861 MaximumCall603Via619From624Chunk07SuffixFrom608From860From861.

Definition values :=
  MaximumCall603Via619From624Chunk07PrefixFrom608From860From861.values ++ MaximumCall603From619From624Leaf61ValueFrom608From860From861.value :: MaximumCall603Via619From624Chunk07SuffixFrom608From860From861.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 7 MaximumCall603Via619From624ContextFrom608From860From861.leaves)
    5 = Some MaximumCall603From619From624Leaf61SplitFrom608From860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 7
    MaximumCall603Via619From624ContextFrom608From860From861.leaves) 5)). Qed.

Lemma values_eq :
  List.map MaximumCall603Via619From624ContextFrom608From860From861.depth
    (MaximumListChunks.chunk_at 7 MaximumCall603Via619From624ContextFrom608From860From861.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall603Via619From624Chunk07PrefixFrom608From860From861.values_eq.
  rewrite <- MaximumCall603Via619From624Chunk07SuffixFrom608From860From861.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall603Via619From624ContextFrom608From860From861.depth (MaximumListChunks.chunk_at 7 MaximumCall603Via619From624ContextFrom608From860From861.leaves)
    5 MaximumCall603From619From624Leaf61SplitFrom608From860From861.leaf MaximumCall603From619From624Leaf61ValueFrom608From860From861.value).
  - exact leaf_lookup.
  - exact MaximumCall603From619From624Leaf61ValueFrom608From860From861.value_eq.
Qed.
