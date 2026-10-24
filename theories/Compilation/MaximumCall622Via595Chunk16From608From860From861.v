From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall622Via595ContextFrom608From860From861 MaximumCall622Leaf130ContextFrom608From860From861 MaximumCall622Leaf130OuterValueFrom608From860From861 MaximumCall622Via595Chunk16PrefixFrom608From860From861 MaximumCall622Via595Chunk16SuffixFrom608From860From861.

Definition values :=
  MaximumCall622Via595Chunk16PrefixFrom608From860From861.values ++ MaximumCall622Leaf130OuterValueFrom608From860From861.value :: MaximumCall622Via595Chunk16SuffixFrom608From860From861.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 16 MaximumCall622Via595ContextFrom608From860From861.leaves)
    2 = Some MaximumCall622Leaf130ContextFrom608From860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 16
    MaximumCall622Via595ContextFrom608From860From861.leaves) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall622Via595ContextFrom608From860From861.depth
    (MaximumListChunks.chunk_at 16 MaximumCall622Via595ContextFrom608From860From861.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall622Via595Chunk16PrefixFrom608From860From861.values_eq.
  rewrite <- MaximumCall622Via595Chunk16SuffixFrom608From860From861.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall622Via595ContextFrom608From860From861.depth (MaximumListChunks.chunk_at 16 MaximumCall622Via595ContextFrom608From860From861.leaves)
    2 MaximumCall622Leaf130ContextFrom608From860From861.leaf MaximumCall622Leaf130OuterValueFrom608From860From861.value).
  - exact leaf_lookup.
  - exact MaximumCall622Leaf130OuterValueFrom608From860From861.value_eq.
Qed.
