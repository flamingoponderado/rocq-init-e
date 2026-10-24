From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall622Via595ContextFrom608From860 MaximumCall622Leaf130ContextFrom608From860 MaximumCall622Leaf130OuterValueFrom608From860 MaximumCall622Via595Chunk16PrefixFrom608From860 MaximumCall622Via595Chunk16SuffixFrom608From860.

Definition values :=
  MaximumCall622Via595Chunk16PrefixFrom608From860.values ++ MaximumCall622Leaf130OuterValueFrom608From860.value :: MaximumCall622Via595Chunk16SuffixFrom608From860.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 16 MaximumCall622Via595ContextFrom608From860.leaves)
    2 = Some MaximumCall622Leaf130ContextFrom608From860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 16
    MaximumCall622Via595ContextFrom608From860.leaves) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall622Via595ContextFrom608From860.depth
    (MaximumListChunks.chunk_at 16 MaximumCall622Via595ContextFrom608From860.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall622Via595Chunk16PrefixFrom608From860.values_eq.
  rewrite <- MaximumCall622Via595Chunk16SuffixFrom608From860.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall622Via595ContextFrom608From860.depth (MaximumListChunks.chunk_at 16 MaximumCall622Via595ContextFrom608From860.leaves)
    2 MaximumCall622Leaf130ContextFrom608From860.leaf MaximumCall622Leaf130OuterValueFrom608From860.value).
  - exact leaf_lookup.
  - exact MaximumCall622Leaf130OuterValueFrom608From860.value_eq.
Qed.
