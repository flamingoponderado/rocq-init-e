From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall598StructuredFrom606ContextFrom608 MaximumCall598From606Leaf77SplitFrom608 MaximumCall598From606Leaf77ValueFrom608 MaximumCall598StructuredFrom606Chunk09PrefixFrom608 MaximumCall598StructuredFrom606Chunk09SuffixFrom608.

Definition values :=
  MaximumCall598StructuredFrom606Chunk09PrefixFrom608.values ++ MaximumCall598From606Leaf77ValueFrom608.value :: MaximumCall598StructuredFrom606Chunk09SuffixFrom608.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom606ContextFrom608.leaves)
    5 = Some MaximumCall598From606Leaf77SplitFrom608.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 9
    MaximumCall598StructuredFrom606ContextFrom608.leaves) 5)). Qed.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom606ContextFrom608.depth
    (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom606ContextFrom608.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall598StructuredFrom606Chunk09PrefixFrom608.values_eq.
  rewrite <- MaximumCall598StructuredFrom606Chunk09SuffixFrom608.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall598StructuredFrom606ContextFrom608.depth (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom606ContextFrom608.leaves)
    5 MaximumCall598From606Leaf77SplitFrom608.leaf MaximumCall598From606Leaf77ValueFrom608.value).
  - exact leaf_lookup.
  - exact MaximumCall598From606Leaf77ValueFrom608.value_eq.
Qed.
