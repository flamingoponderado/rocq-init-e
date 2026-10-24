From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall622Leaf130ContextFrom608From860 MaximumCall622Inner54SplitFrom608From860 MaximumCall622Inner54ValueFrom608From860 MaximumCall622Leaf130Chunk06PrefixFrom608From860 MaximumCall622Leaf130Chunk06SuffixFrom608From860.

Definition values :=
  MaximumCall622Leaf130Chunk06PrefixFrom608From860.values ++ MaximumCall622Inner54ValueFrom608From860.value :: MaximumCall622Leaf130Chunk06SuffixFrom608From860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 6 MaximumCall622Leaf130ContextFrom608From860.leaves)
    6 = Some MaximumCall622Inner54SplitFrom608From860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 6
    MaximumCall622Leaf130ContextFrom608From860.leaves) 6)). Qed.

Lemma values_eq :
  List.map MaximumCall622Leaf130ContextFrom608From860.depth
    (MaximumListChunks.chunk_at 6 MaximumCall622Leaf130ContextFrom608From860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall622Leaf130Chunk06PrefixFrom608From860.values_eq.
  rewrite <- MaximumCall622Leaf130Chunk06SuffixFrom608From860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall622Leaf130ContextFrom608From860.depth (MaximumListChunks.chunk_at 6 MaximumCall622Leaf130ContextFrom608From860.leaves)
    6 MaximumCall622Inner54SplitFrom608From860.leaf MaximumCall622Inner54ValueFrom608From860.value).
  - exact leaf_lookup.
  - exact MaximumCall622Inner54ValueFrom608From860.value_eq.
Qed.
