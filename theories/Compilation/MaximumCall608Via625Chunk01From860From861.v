From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall608Via625ContextFrom860From861 MaximumCall608Leaf15SplitFrom860From861 MaximumCall608Leaf15ValueFrom860From861 MaximumCall608Via625Chunk01PrefixFrom860From861 MaximumCall608Via625Chunk01SuffixFrom860From861.

Definition values :=
  MaximumCall608Via625Chunk01PrefixFrom860From861.values ++ MaximumCall608Leaf15ValueFrom860From861.value :: MaximumCall608Via625Chunk01SuffixFrom860From861.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 1 MaximumCall608Via625ContextFrom860From861.leaves)
    7 = Some MaximumCall608Leaf15SplitFrom860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 1
    MaximumCall608Via625ContextFrom860From861.leaves) 7)). Qed.

Lemma values_eq :
  List.map MaximumCall608Via625ContextFrom860From861.depth
    (MaximumListChunks.chunk_at 1 MaximumCall608Via625ContextFrom860From861.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall608Via625Chunk01PrefixFrom860From861.values_eq.
  rewrite <- MaximumCall608Via625Chunk01SuffixFrom860From861.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall608Via625ContextFrom860From861.depth (MaximumListChunks.chunk_at 1 MaximumCall608Via625ContextFrom860From861.leaves)
    7 MaximumCall608Leaf15SplitFrom860From861.leaf MaximumCall608Leaf15ValueFrom860From861.value).
  - exact leaf_lookup.
  - exact MaximumCall608Leaf15ValueFrom860From861.value_eq.
Qed.
