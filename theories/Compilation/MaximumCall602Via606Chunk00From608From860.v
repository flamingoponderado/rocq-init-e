From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall602Via606ContextFrom608From860 MaximumCall602Leaf04AliasFrom608From860 MaximumCall602Leaf04OuterValueFrom608From860 MaximumCall602Via606Chunk00PrefixFrom608From860 MaximumCall602Via606Chunk00SuffixFrom608From860.

Definition values :=
  MaximumCall602Via606Chunk00PrefixFrom608From860.values ++ MaximumCall602Leaf04OuterValueFrom608From860.value :: MaximumCall602Via606Chunk00SuffixFrom608From860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 0 MaximumCall602Via606ContextFrom608From860.leaves)
    4 = Some MaximumCall602Leaf04AliasFrom608From860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 0
    MaximumCall602Via606ContextFrom608From860.leaves) 4)). Qed.

Lemma values_eq :
  List.map MaximumCall602Via606ContextFrom608From860.depth
    (MaximumListChunks.chunk_at 0 MaximumCall602Via606ContextFrom608From860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall602Via606Chunk00PrefixFrom608From860.values_eq.
  rewrite <- MaximumCall602Via606Chunk00SuffixFrom608From860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall602Via606ContextFrom608From860.depth (MaximumListChunks.chunk_at 0 MaximumCall602Via606ContextFrom608From860.leaves)
    4 MaximumCall602Leaf04AliasFrom608From860.leaf MaximumCall602Leaf04OuterValueFrom608From860.value).
  - exact leaf_lookup.
  - exact MaximumCall602Leaf04OuterValueFrom608From860.value_eq.
Qed.
