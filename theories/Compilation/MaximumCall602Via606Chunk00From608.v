From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall602Via606ContextFrom608 MaximumCall602Leaf04AliasFrom608 MaximumCall602Leaf04OuterValueFrom608 MaximumCall602Via606Chunk00PrefixFrom608 MaximumCall602Via606Chunk00SuffixFrom608.

Definition values :=
  MaximumCall602Via606Chunk00PrefixFrom608.values ++ MaximumCall602Leaf04OuterValueFrom608.value :: MaximumCall602Via606Chunk00SuffixFrom608.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 0 MaximumCall602Via606ContextFrom608.leaves)
    4 = Some MaximumCall602Leaf04AliasFrom608.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 0
    MaximumCall602Via606ContextFrom608.leaves) 4)). Qed.

Lemma values_eq :
  List.map MaximumCall602Via606ContextFrom608.depth
    (MaximumListChunks.chunk_at 0 MaximumCall602Via606ContextFrom608.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall602Via606Chunk00PrefixFrom608.values_eq.
  rewrite <- MaximumCall602Via606Chunk00SuffixFrom608.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall602Via606ContextFrom608.depth (MaximumListChunks.chunk_at 0 MaximumCall602Via606ContextFrom608.leaves)
    4 MaximumCall602Leaf04AliasFrom608.leaf MaximumCall602Leaf04OuterValueFrom608.value).
  - exact leaf_lookup.
  - exact MaximumCall602Leaf04OuterValueFrom608.value_eq.
Qed.
