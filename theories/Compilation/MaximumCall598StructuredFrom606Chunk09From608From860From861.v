From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall598StructuredFrom606ContextFrom608From860From861 MaximumCall598From606Leaf77SplitFrom608From860From861 MaximumCall598From606Leaf77ValueFrom608From860From861 MaximumCall598StructuredFrom606Chunk09PrefixFrom608From860From861 MaximumCall598StructuredFrom606Chunk09SuffixFrom608From860From861.

Definition values :=
  MaximumCall598StructuredFrom606Chunk09PrefixFrom608From860From861.values ++ MaximumCall598From606Leaf77ValueFrom608From860From861.value :: MaximumCall598StructuredFrom606Chunk09SuffixFrom608From860From861.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom606ContextFrom608From860From861.leaves)
    5 = Some MaximumCall598From606Leaf77SplitFrom608From860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 9
    MaximumCall598StructuredFrom606ContextFrom608From860From861.leaves) 5)). Qed.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom606ContextFrom608From860From861.depth
    (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom606ContextFrom608From860From861.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall598StructuredFrom606Chunk09PrefixFrom608From860From861.values_eq.
  rewrite <- MaximumCall598StructuredFrom606Chunk09SuffixFrom608From860From861.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall598StructuredFrom606ContextFrom608From860From861.depth (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom606ContextFrom608From860From861.leaves)
    5 MaximumCall598From606Leaf77SplitFrom608From860From861.leaf MaximumCall598From606Leaf77ValueFrom608From860From861.value).
  - exact leaf_lookup.
  - exact MaximumCall598From606Leaf77ValueFrom608From860From861.value_eq.
Qed.
