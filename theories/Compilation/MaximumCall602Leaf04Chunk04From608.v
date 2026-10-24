From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall602Leaf04ContextFrom608 MaximumCall602Inner35SplitFrom608 MaximumCall602Inner35ValueFrom608 MaximumCall602Leaf04Chunk04PrefixFrom608 MaximumCall602Leaf04Chunk04SuffixFrom608.

Definition values :=
  MaximumCall602Leaf04Chunk04PrefixFrom608.values ++ MaximumCall602Inner35ValueFrom608.value :: MaximumCall602Leaf04Chunk04SuffixFrom608.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 4 MaximumCall602Leaf04ContextFrom608.leaves)
    3 = Some MaximumCall602Inner35SplitFrom608.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 4
    MaximumCall602Leaf04ContextFrom608.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall602Leaf04ContextFrom608.depth
    (MaximumListChunks.chunk_at 4 MaximumCall602Leaf04ContextFrom608.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall602Leaf04Chunk04PrefixFrom608.values_eq.
  rewrite <- MaximumCall602Leaf04Chunk04SuffixFrom608.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall602Leaf04ContextFrom608.depth (MaximumListChunks.chunk_at 4 MaximumCall602Leaf04ContextFrom608.leaves)
    3 MaximumCall602Inner35SplitFrom608.leaf MaximumCall602Inner35ValueFrom608.value).
  - exact leaf_lookup.
  - exact MaximumCall602Inner35ValueFrom608.value_eq.
Qed.
