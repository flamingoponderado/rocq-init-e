From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall606Via608ContextFrom860From861 MaximumCall606Leaf34SplitFrom608From860From861 MaximumCall606Leaf34ValueFrom608From860From861 MaximumCall606Leaf37SplitFrom608From860From861 MaximumCall606Leaf37ValueFrom608From860From861
  MaximumCall606Via608Chunk04PrefixFrom860From861 MaximumCall606Via608Chunk04MiddleFrom860From861 MaximumCall606Via608Chunk04SuffixFrom860From861.

Definition values :=
  MaximumCall606Via608Chunk04PrefixFrom860From861.values ++
  (MaximumCall606Leaf34ValueFrom608From860From861.value ::
    (MaximumCall606Via608Chunk04MiddleFrom860From861.values ++
      (MaximumCall606Leaf37ValueFrom608From860From861.value :: MaximumCall606Via608Chunk04SuffixFrom860From861.values))).

Lemma first_lookup : List.nth_error (MaximumListChunks.chunk_at 4 MaximumCall606Via608ContextFrom860From861.leaves) 2 = Some MaximumCall606Leaf34SplitFrom608From860From861.leaf.
Proof. vm_cast_no_check (eq_refl (List.nth_error (MaximumListChunks.chunk_at 4 MaximumCall606Via608ContextFrom860From861.leaves) 2)). Qed.

Lemma second_lookup :
  List.nth_error (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via608ContextFrom860From861.leaves)) 2 = Some MaximumCall606Leaf37SplitFrom608From860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via608ContextFrom860From861.leaves)) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall606Via608ContextFrom860From861.depth (MaximumListChunks.chunk_at 4 MaximumCall606Via608ContextFrom860From861.leaves) = values.
Proof.
  unfold values.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall606Via608ContextFrom860From861.depth (MaximumListChunks.chunk_at 4 MaximumCall606Via608ContextFrom860From861.leaves) 2
    MaximumCall606Leaf34SplitFrom608From860From861.leaf MaximumCall606Leaf34ValueFrom608From860From861.value
    first_lookup MaximumCall606Leaf34ValueFrom608From860From861.value_eq) as Hfirst.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall606Via608ContextFrom860From861.depth (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via608ContextFrom860From861.leaves)) 2
    MaximumCall606Leaf37SplitFrom608From860From861.leaf MaximumCall606Leaf37ValueFrom608From860From861.value
    second_lookup MaximumCall606Leaf37ValueFrom608From860From861.value_eq) as Hsecond.
  rewrite Hfirst, Hsecond.
  rewrite MaximumCall606Via608Chunk04PrefixFrom860From861.values_eq, MaximumCall606Via608Chunk04MiddleFrom860From861.values_eq,
    MaximumCall606Via608Chunk04SuffixFrom860From861.values_eq.
  reflexivity.
Qed.
