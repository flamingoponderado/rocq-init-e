From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall623Via595ContextFrom608 MaximumCall623Leaf131SplitFrom608 MaximumCall623Leaf131ValueFrom608 MaximumCall623Via595Chunk16PrefixFrom608 MaximumCall623Via595Chunk16SuffixFrom608.

Definition values :=
  MaximumCall623Via595Chunk16PrefixFrom608.values ++ MaximumCall623Leaf131ValueFrom608.value :: MaximumCall623Via595Chunk16SuffixFrom608.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 16 MaximumCall623Via595ContextFrom608.leaves)
    3 = Some MaximumCall623Leaf131SplitFrom608.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 16
    MaximumCall623Via595ContextFrom608.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall623Via595ContextFrom608.depth
    (MaximumListChunks.chunk_at 16 MaximumCall623Via595ContextFrom608.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall623Via595Chunk16PrefixFrom608.values_eq.
  rewrite <- MaximumCall623Via595Chunk16SuffixFrom608.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall623Via595ContextFrom608.depth (MaximumListChunks.chunk_at 16 MaximumCall623Via595ContextFrom608.leaves)
    3 MaximumCall623Leaf131SplitFrom608.leaf MaximumCall623Leaf131ValueFrom608.value).
  - exact leaf_lookup.
  - exact MaximumCall623Leaf131ValueFrom608.value_eq.
Qed.
