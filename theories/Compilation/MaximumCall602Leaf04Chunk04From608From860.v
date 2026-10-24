From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall602Leaf04ContextFrom608From860 MaximumCall602Inner35SplitFrom608From860 MaximumCall602Inner35ValueFrom608From860 MaximumCall602Leaf04Chunk04PrefixFrom608From860 MaximumCall602Leaf04Chunk04SuffixFrom608From860.

Definition values :=
  MaximumCall602Leaf04Chunk04PrefixFrom608From860.values ++ MaximumCall602Inner35ValueFrom608From860.value :: MaximumCall602Leaf04Chunk04SuffixFrom608From860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 4 MaximumCall602Leaf04ContextFrom608From860.leaves)
    3 = Some MaximumCall602Inner35SplitFrom608From860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 4
    MaximumCall602Leaf04ContextFrom608From860.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall602Leaf04ContextFrom608From860.depth
    (MaximumListChunks.chunk_at 4 MaximumCall602Leaf04ContextFrom608From860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall602Leaf04Chunk04PrefixFrom608From860.values_eq.
  rewrite <- MaximumCall602Leaf04Chunk04SuffixFrom608From860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall602Leaf04ContextFrom608From860.depth (MaximumListChunks.chunk_at 4 MaximumCall602Leaf04ContextFrom608From860.leaves)
    3 MaximumCall602Inner35SplitFrom608From860.leaf MaximumCall602Inner35ValueFrom608From860.value).
  - exact leaf_lookup.
  - exact MaximumCall602Inner35ValueFrom608From860.value_eq.
Qed.
