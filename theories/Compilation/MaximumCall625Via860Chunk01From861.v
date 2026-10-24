From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall625Via860ContextFrom861 MaximumCall625Leaf08SplitFrom860From861 MaximumCall625Leaf08ValueFrom860From861 MaximumCall625Leaf13AliasFrom860From861 MaximumCall625Leaf13OuterValueFrom860From861
  MaximumCall625Via860Chunk01PrefixFrom861 MaximumCall625Via860Chunk01MiddleFrom861 MaximumCall625Via860Chunk01SuffixFrom861.

Definition values :=
  MaximumCall625Via860Chunk01PrefixFrom861.values ++
  (MaximumCall625Leaf08ValueFrom860From861.value ::
    (MaximumCall625Via860Chunk01MiddleFrom861.values ++
      (MaximumCall625Leaf13OuterValueFrom860From861.value :: MaximumCall625Via860Chunk01SuffixFrom861.values))).

Lemma first_lookup : List.nth_error (MaximumListChunks.chunk_at 1 MaximumCall625Via860ContextFrom861.leaves) 0 = Some MaximumCall625Leaf08SplitFrom860From861.leaf.
Proof. vm_cast_no_check (eq_refl (List.nth_error (MaximumListChunks.chunk_at 1 MaximumCall625Via860ContextFrom861.leaves) 0)). Qed.

Lemma second_lookup :
  List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 1 MaximumCall625Via860ContextFrom861.leaves)) 4 = Some MaximumCall625Leaf13AliasFrom860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 1 MaximumCall625Via860ContextFrom861.leaves)) 4)). Qed.

Lemma values_eq :
  List.map MaximumCall625Via860ContextFrom861.depth (MaximumListChunks.chunk_at 1 MaximumCall625Via860ContextFrom861.leaves) = values.
Proof.
  unfold values.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall625Via860ContextFrom861.depth (MaximumListChunks.chunk_at 1 MaximumCall625Via860ContextFrom861.leaves) 0
    MaximumCall625Leaf08SplitFrom860From861.leaf MaximumCall625Leaf08ValueFrom860From861.value
    first_lookup MaximumCall625Leaf08ValueFrom860From861.value_eq) as Hfirst.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall625Via860ContextFrom861.depth (List.skipn 1 (MaximumListChunks.chunk_at 1 MaximumCall625Via860ContextFrom861.leaves)) 4
    MaximumCall625Leaf13AliasFrom860From861.leaf MaximumCall625Leaf13OuterValueFrom860From861.value
    second_lookup MaximumCall625Leaf13OuterValueFrom860From861.value_eq) as Hsecond.
  rewrite Hfirst, Hsecond.
  rewrite MaximumCall625Via860Chunk01PrefixFrom861.values_eq, MaximumCall625Via860Chunk01MiddleFrom861.values_eq,
    MaximumCall625Via860Chunk01SuffixFrom861.values_eq.
  reflexivity.
Qed.
