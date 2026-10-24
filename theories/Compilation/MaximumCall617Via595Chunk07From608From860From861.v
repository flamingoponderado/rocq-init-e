From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall617Via595ContextFrom608From860From861 MaximumCall617Leaf59SplitFrom608From860From861 MaximumCall617Leaf59ValueFrom608From860From861 MaximumCall617Via595Chunk07PrefixFrom608From860From861 MaximumCall617Via595Chunk07SuffixFrom608From860From861.

Definition values :=
  MaximumCall617Via595Chunk07PrefixFrom608From860From861.values ++ MaximumCall617Leaf59ValueFrom608From860From861.value :: MaximumCall617Via595Chunk07SuffixFrom608From860From861.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 7 MaximumCall617Via595ContextFrom608From860From861.leaves)
    3 = Some MaximumCall617Leaf59SplitFrom608From860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 7
    MaximumCall617Via595ContextFrom608From860From861.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall617Via595ContextFrom608From860From861.depth
    (MaximumListChunks.chunk_at 7 MaximumCall617Via595ContextFrom608From860From861.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall617Via595Chunk07PrefixFrom608From860From861.values_eq.
  rewrite <- MaximumCall617Via595Chunk07SuffixFrom608From860From861.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall617Via595ContextFrom608From860From861.depth (MaximumListChunks.chunk_at 7 MaximumCall617Via595ContextFrom608From860From861.leaves)
    3 MaximumCall617Leaf59SplitFrom608From860From861.leaf MaximumCall617Leaf59ValueFrom608From860From861.value).
  - exact leaf_lookup.
  - exact MaximumCall617Leaf59ValueFrom608From860From861.value_eq.
Qed.
