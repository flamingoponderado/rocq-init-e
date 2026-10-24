From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall595StructuredContextFrom608 MaximumCall595Leaf1019SplitFrom608 MaximumCall595Leaf1019ValueFrom608 MaximumCall595StructuredChunk127PrefixFrom608 MaximumCall595StructuredChunk127SuffixFrom608.

Definition values :=
  MaximumCall595StructuredChunk127PrefixFrom608.values ++ MaximumCall595Leaf1019ValueFrom608.value :: MaximumCall595StructuredChunk127SuffixFrom608.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 127 MaximumCall595StructuredContextFrom608.leaves)
    3 = Some MaximumCall595Leaf1019SplitFrom608.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 127
    MaximumCall595StructuredContextFrom608.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall595StructuredContextFrom608.depth
    (MaximumListChunks.chunk_at 127 MaximumCall595StructuredContextFrom608.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall595StructuredChunk127PrefixFrom608.values_eq.
  rewrite <- MaximumCall595StructuredChunk127SuffixFrom608.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall595StructuredContextFrom608.depth (MaximumListChunks.chunk_at 127 MaximumCall595StructuredContextFrom608.leaves)
    3 MaximumCall595Leaf1019SplitFrom608.leaf MaximumCall595Leaf1019ValueFrom608.value).
  - exact leaf_lookup.
  - exact MaximumCall595Leaf1019ValueFrom608.value_eq.
Qed.
