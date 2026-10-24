From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall622Leaf130ContextFrom860From861 MaximumCall622Inner54SplitFrom860From861 MaximumCall622Inner54ValueFrom860From861 MaximumCall622Leaf130Chunk06PrefixFrom860From861 MaximumCall622Leaf130Chunk06SuffixFrom860From861.

Definition values :=
  MaximumCall622Leaf130Chunk06PrefixFrom860From861.values ++ MaximumCall622Inner54ValueFrom860From861.value :: MaximumCall622Leaf130Chunk06SuffixFrom860From861.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 6 MaximumCall622Leaf130ContextFrom860From861.leaves)
    6 = Some MaximumCall622Inner54SplitFrom860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 6
    MaximumCall622Leaf130ContextFrom860From861.leaves) 6)). Qed.

Lemma values_eq :
  List.map MaximumCall622Leaf130ContextFrom860From861.depth
    (MaximumListChunks.chunk_at 6 MaximumCall622Leaf130ContextFrom860From861.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall622Leaf130Chunk06PrefixFrom860From861.values_eq.
  rewrite <- MaximumCall622Leaf130Chunk06SuffixFrom860From861.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall622Leaf130ContextFrom860From861.depth (MaximumListChunks.chunk_at 6 MaximumCall622Leaf130ContextFrom860From861.leaves)
    6 MaximumCall622Inner54SplitFrom860From861.leaf MaximumCall622Inner54ValueFrom860From861.value).
  - exact leaf_lookup.
  - exact MaximumCall622Inner54ValueFrom860From861.value_eq.
Qed.
