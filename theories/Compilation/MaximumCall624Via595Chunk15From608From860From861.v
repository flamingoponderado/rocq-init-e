From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall624Via595ContextFrom608From860From861 MaximumCall624Leaf125SplitFrom608From860From861 MaximumCall624Leaf125ValueFrom608From860From861 MaximumCall624Via595Chunk15PrefixFrom608From860From861 MaximumCall624Via595Chunk15SuffixFrom608From860From861.

Definition values :=
  MaximumCall624Via595Chunk15PrefixFrom608From860From861.values ++ MaximumCall624Leaf125ValueFrom608From860From861.value :: MaximumCall624Via595Chunk15SuffixFrom608From860From861.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 15 MaximumCall624Via595ContextFrom608From860From861.leaves)
    5 = Some MaximumCall624Leaf125SplitFrom608From860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 15
    MaximumCall624Via595ContextFrom608From860From861.leaves) 5)). Qed.

Lemma values_eq :
  List.map MaximumCall624Via595ContextFrom608From860From861.depth
    (MaximumListChunks.chunk_at 15 MaximumCall624Via595ContextFrom608From860From861.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall624Via595Chunk15PrefixFrom608From860From861.values_eq.
  rewrite <- MaximumCall624Via595Chunk15SuffixFrom608From860From861.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall624Via595ContextFrom608From860From861.depth (MaximumListChunks.chunk_at 15 MaximumCall624Via595ContextFrom608From860From861.leaves)
    5 MaximumCall624Leaf125SplitFrom608From860From861.leaf MaximumCall624Leaf125ValueFrom608From860From861.value).
  - exact leaf_lookup.
  - exact MaximumCall624Leaf125ValueFrom608From860From861.value_eq.
Qed.
