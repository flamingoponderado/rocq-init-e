From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall621Via595ContextFrom860 MaximumCall621Leaf148ContextFrom860 MaximumCall621Leaf148OuterValueFrom860 MaximumCall621Via595Chunk18PrefixFrom860 MaximumCall621Via595Chunk18SuffixFrom860.

Definition values :=
  MaximumCall621Via595Chunk18PrefixFrom860.values ++ MaximumCall621Leaf148OuterValueFrom860.value :: MaximumCall621Via595Chunk18SuffixFrom860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 18 MaximumCall621Via595ContextFrom860.leaves)
    4 = Some MaximumCall621Leaf148ContextFrom860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 18
    MaximumCall621Via595ContextFrom860.leaves) 4)). Qed.

Lemma values_eq :
  List.map MaximumCall621Via595ContextFrom860.depth
    (MaximumListChunks.chunk_at 18 MaximumCall621Via595ContextFrom860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall621Via595Chunk18PrefixFrom860.values_eq.
  rewrite <- MaximumCall621Via595Chunk18SuffixFrom860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall621Via595ContextFrom860.depth (MaximumListChunks.chunk_at 18 MaximumCall621Via595ContextFrom860.leaves)
    4 MaximumCall621Leaf148ContextFrom860.leaf MaximumCall621Leaf148OuterValueFrom860.value).
  - exact leaf_lookup.
  - exact MaximumCall621Leaf148OuterValueFrom860.value_eq.
Qed.
