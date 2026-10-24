From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall608Via625ContextFrom860 MaximumCall608Leaf15SplitFrom860 MaximumCall608Leaf15ValueFrom860 MaximumCall608Via625Chunk01PrefixFrom860 MaximumCall608Via625Chunk01SuffixFrom860.

Definition values :=
  MaximumCall608Via625Chunk01PrefixFrom860.values ++ MaximumCall608Leaf15ValueFrom860.value :: MaximumCall608Via625Chunk01SuffixFrom860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 1 MaximumCall608Via625ContextFrom860.leaves)
    7 = Some MaximumCall608Leaf15SplitFrom860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 1
    MaximumCall608Via625ContextFrom860.leaves) 7)). Qed.

Lemma values_eq :
  List.map MaximumCall608Via625ContextFrom860.depth
    (MaximumListChunks.chunk_at 1 MaximumCall608Via625ContextFrom860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall608Via625Chunk01PrefixFrom860.values_eq.
  rewrite <- MaximumCall608Via625Chunk01SuffixFrom860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall608Via625ContextFrom860.depth (MaximumListChunks.chunk_at 1 MaximumCall608Via625ContextFrom860.leaves)
    7 MaximumCall608Leaf15SplitFrom860.leaf MaximumCall608Leaf15ValueFrom860.value).
  - exact leaf_lookup.
  - exact MaximumCall608Leaf15ValueFrom860.value_eq.
Qed.
