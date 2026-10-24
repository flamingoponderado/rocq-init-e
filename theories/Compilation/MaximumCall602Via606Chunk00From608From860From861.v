From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall602Via606ContextFrom608From860From861 MaximumCall602Leaf04AliasFrom608From860From861 MaximumCall602Leaf04OuterValueFrom608From860From861 MaximumCall602Via606Chunk00PrefixFrom608From860From861 MaximumCall602Via606Chunk00SuffixFrom608From860From861.

Definition values :=
  MaximumCall602Via606Chunk00PrefixFrom608From860From861.values ++ MaximumCall602Leaf04OuterValueFrom608From860From861.value :: MaximumCall602Via606Chunk00SuffixFrom608From860From861.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 0 MaximumCall602Via606ContextFrom608From860From861.leaves)
    4 = Some MaximumCall602Leaf04AliasFrom608From860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 0
    MaximumCall602Via606ContextFrom608From860From861.leaves) 4)). Qed.

Lemma values_eq :
  List.map MaximumCall602Via606ContextFrom608From860From861.depth
    (MaximumListChunks.chunk_at 0 MaximumCall602Via606ContextFrom608From860From861.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall602Via606Chunk00PrefixFrom608From860From861.values_eq.
  rewrite <- MaximumCall602Via606Chunk00SuffixFrom608From860From861.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall602Via606ContextFrom608From860From861.depth (MaximumListChunks.chunk_at 0 MaximumCall602Via606ContextFrom608From860From861.leaves)
    4 MaximumCall602Leaf04AliasFrom608From860From861.leaf MaximumCall602Leaf04OuterValueFrom608From860From861.value).
  - exact leaf_lookup.
  - exact MaximumCall602Leaf04OuterValueFrom608From860From861.value_eq.
Qed.
