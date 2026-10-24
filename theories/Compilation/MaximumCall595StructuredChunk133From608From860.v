From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall595StructuredContextFrom608From860 MaximumCall595Leaf1067SplitFrom608From860 MaximumCall595Leaf1067ValueFrom608From860 MaximumCall595StructuredChunk133PrefixFrom608From860 MaximumCall595StructuredChunk133SuffixFrom608From860.

Definition values :=
  MaximumCall595StructuredChunk133PrefixFrom608From860.values ++ MaximumCall595Leaf1067ValueFrom608From860.value :: MaximumCall595StructuredChunk133SuffixFrom608From860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 133 MaximumCall595StructuredContextFrom608From860.leaves)
    3 = Some MaximumCall595Leaf1067SplitFrom608From860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 133
    MaximumCall595StructuredContextFrom608From860.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall595StructuredContextFrom608From860.depth
    (MaximumListChunks.chunk_at 133 MaximumCall595StructuredContextFrom608From860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall595StructuredChunk133PrefixFrom608From860.values_eq.
  rewrite <- MaximumCall595StructuredChunk133SuffixFrom608From860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall595StructuredContextFrom608From860.depth (MaximumListChunks.chunk_at 133 MaximumCall595StructuredContextFrom608From860.leaves)
    3 MaximumCall595Leaf1067SplitFrom608From860.leaf MaximumCall595Leaf1067ValueFrom608From860.value).
  - exact leaf_lookup.
  - exact MaximumCall595Leaf1067ValueFrom608From860.value_eq.
Qed.
