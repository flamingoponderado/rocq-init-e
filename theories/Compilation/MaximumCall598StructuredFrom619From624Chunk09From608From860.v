From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall598StructuredFrom619From624ContextFrom608From860 MaximumCall598From619From624Leaf77SplitFrom608From860 MaximumCall598From619From624Leaf77ValueFrom608From860 MaximumCall598StructuredFrom619From624Chunk09PrefixFrom608From860 MaximumCall598StructuredFrom619From624Chunk09SuffixFrom608From860.

Definition values :=
  MaximumCall598StructuredFrom619From624Chunk09PrefixFrom608From860.values ++ MaximumCall598From619From624Leaf77ValueFrom608From860.value :: MaximumCall598StructuredFrom619From624Chunk09SuffixFrom608From860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom619From624ContextFrom608From860.leaves)
    5 = Some MaximumCall598From619From624Leaf77SplitFrom608From860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 9
    MaximumCall598StructuredFrom619From624ContextFrom608From860.leaves) 5)). Qed.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom619From624ContextFrom608From860.depth
    (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom619From624ContextFrom608From860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall598StructuredFrom619From624Chunk09PrefixFrom608From860.values_eq.
  rewrite <- MaximumCall598StructuredFrom619From624Chunk09SuffixFrom608From860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall598StructuredFrom619From624ContextFrom608From860.depth (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom619From624ContextFrom608From860.leaves)
    5 MaximumCall598From619From624Leaf77SplitFrom608From860.leaf MaximumCall598From619From624Leaf77ValueFrom608From860.value).
  - exact leaf_lookup.
  - exact MaximumCall598From619From624Leaf77ValueFrom608From860.value_eq.
Qed.
