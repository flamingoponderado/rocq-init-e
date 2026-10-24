From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall621Via595ContextFrom608 MaximumCall621Leaf148ContextFrom608 MaximumCall621Leaf148OuterValueFrom608 MaximumCall621Via595Chunk18PrefixFrom608 MaximumCall621Via595Chunk18SuffixFrom608.

Definition values :=
  MaximumCall621Via595Chunk18PrefixFrom608.values ++ MaximumCall621Leaf148OuterValueFrom608.value :: MaximumCall621Via595Chunk18SuffixFrom608.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 18 MaximumCall621Via595ContextFrom608.leaves)
    4 = Some MaximumCall621Leaf148ContextFrom608.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 18
    MaximumCall621Via595ContextFrom608.leaves) 4)). Qed.

Lemma values_eq :
  List.map MaximumCall621Via595ContextFrom608.depth
    (MaximumListChunks.chunk_at 18 MaximumCall621Via595ContextFrom608.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall621Via595Chunk18PrefixFrom608.values_eq.
  rewrite <- MaximumCall621Via595Chunk18SuffixFrom608.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall621Via595ContextFrom608.depth (MaximumListChunks.chunk_at 18 MaximumCall621Via595ContextFrom608.leaves)
    4 MaximumCall621Leaf148ContextFrom608.leaf MaximumCall621Leaf148OuterValueFrom608.value).
  - exact leaf_lookup.
  - exact MaximumCall621Leaf148OuterValueFrom608.value_eq.
Qed.
