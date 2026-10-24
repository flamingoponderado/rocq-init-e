From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall595StructuredContextFrom860 MaximumCall595Leaf1055SplitFrom860 MaximumCall595Leaf1055ValueFrom860 MaximumCall595StructuredChunk131PrefixFrom860 MaximumCall595StructuredChunk131SuffixFrom860.

Definition values :=
  MaximumCall595StructuredChunk131PrefixFrom860.values ++ MaximumCall595Leaf1055ValueFrom860.value :: MaximumCall595StructuredChunk131SuffixFrom860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 131 MaximumCall595StructuredContextFrom860.leaves)
    7 = Some MaximumCall595Leaf1055SplitFrom860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 131
    MaximumCall595StructuredContextFrom860.leaves) 7)). Qed.

Lemma values_eq :
  List.map MaximumCall595StructuredContextFrom860.depth
    (MaximumListChunks.chunk_at 131 MaximumCall595StructuredContextFrom860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall595StructuredChunk131PrefixFrom860.values_eq.
  rewrite <- MaximumCall595StructuredChunk131SuffixFrom860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall595StructuredContextFrom860.depth (MaximumListChunks.chunk_at 131 MaximumCall595StructuredContextFrom860.leaves)
    7 MaximumCall595Leaf1055SplitFrom860.leaf MaximumCall595Leaf1055ValueFrom860.value).
  - exact leaf_lookup.
  - exact MaximumCall595Leaf1055ValueFrom860.value_eq.
Qed.
