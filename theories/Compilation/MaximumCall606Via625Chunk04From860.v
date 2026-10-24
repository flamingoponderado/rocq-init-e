From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall606Via625ContextFrom860 MaximumCall606Leaf34SplitFrom860 MaximumCall606Leaf34ValueFrom860 MaximumCall606Leaf37SplitFrom860 MaximumCall606Leaf37ValueFrom860
  MaximumCall606Via625Chunk04PrefixFrom860 MaximumCall606Via625Chunk04MiddleFrom860 MaximumCall606Via625Chunk04SuffixFrom860.

Definition values :=
  MaximumCall606Via625Chunk04PrefixFrom860.values ++
  (MaximumCall606Leaf34ValueFrom860.value ::
    (MaximumCall606Via625Chunk04MiddleFrom860.values ++
      (MaximumCall606Leaf37ValueFrom860.value :: MaximumCall606Via625Chunk04SuffixFrom860.values))).

Lemma first_lookup : List.nth_error (MaximumListChunks.chunk_at 4 MaximumCall606Via625ContextFrom860.leaves) 2 = Some MaximumCall606Leaf34SplitFrom860.leaf.
Proof. vm_cast_no_check (eq_refl (List.nth_error (MaximumListChunks.chunk_at 4 MaximumCall606Via625ContextFrom860.leaves) 2)). Qed.

Lemma second_lookup :
  List.nth_error (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via625ContextFrom860.leaves)) 2 = Some MaximumCall606Leaf37SplitFrom860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via625ContextFrom860.leaves)) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall606Via625ContextFrom860.depth (MaximumListChunks.chunk_at 4 MaximumCall606Via625ContextFrom860.leaves) = values.
Proof.
  unfold values.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall606Via625ContextFrom860.depth (MaximumListChunks.chunk_at 4 MaximumCall606Via625ContextFrom860.leaves) 2
    MaximumCall606Leaf34SplitFrom860.leaf MaximumCall606Leaf34ValueFrom860.value
    first_lookup MaximumCall606Leaf34ValueFrom860.value_eq) as Hfirst.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall606Via625ContextFrom860.depth (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via625ContextFrom860.leaves)) 2
    MaximumCall606Leaf37SplitFrom860.leaf MaximumCall606Leaf37ValueFrom860.value
    second_lookup MaximumCall606Leaf37ValueFrom860.value_eq) as Hsecond.
  rewrite Hfirst, Hsecond.
  rewrite MaximumCall606Via625Chunk04PrefixFrom860.values_eq, MaximumCall606Via625Chunk04MiddleFrom860.values_eq,
    MaximumCall606Via625Chunk04SuffixFrom860.values_eq.
  reflexivity.
Qed.
