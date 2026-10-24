From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall625Leaf13ContextFrom860From861 MaximumCall625Inner40SplitFrom860From861 MaximumCall625Inner40ValueFrom860From861 MaximumCall625Inner45SplitFrom860From861 MaximumCall625Inner45ValueFrom860From861
  MaximumCall625Leaf13Chunk05PrefixFrom860From861 MaximumCall625Leaf13Chunk05MiddleFrom860From861 MaximumCall625Leaf13Chunk05SuffixFrom860From861.

Definition values :=
  MaximumCall625Leaf13Chunk05PrefixFrom860From861.values ++
  (MaximumCall625Inner40ValueFrom860From861.value ::
    (MaximumCall625Leaf13Chunk05MiddleFrom860From861.values ++
      (MaximumCall625Inner45ValueFrom860From861.value :: MaximumCall625Leaf13Chunk05SuffixFrom860From861.values))).

Lemma first_lookup : List.nth_error (MaximumListChunks.chunk_at 5 MaximumCall625Leaf13ContextFrom860From861.leaves) 0 = Some MaximumCall625Inner40SplitFrom860From861.leaf.
Proof. vm_cast_no_check (eq_refl (List.nth_error (MaximumListChunks.chunk_at 5 MaximumCall625Leaf13ContextFrom860From861.leaves) 0)). Qed.

Lemma second_lookup :
  List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 5 MaximumCall625Leaf13ContextFrom860From861.leaves)) 4 = Some MaximumCall625Inner45SplitFrom860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 5 MaximumCall625Leaf13ContextFrom860From861.leaves)) 4)). Qed.

Lemma values_eq :
  List.map MaximumCall625Leaf13ContextFrom860From861.depth (MaximumListChunks.chunk_at 5 MaximumCall625Leaf13ContextFrom860From861.leaves) = values.
Proof.
  unfold values.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall625Leaf13ContextFrom860From861.depth (MaximumListChunks.chunk_at 5 MaximumCall625Leaf13ContextFrom860From861.leaves) 0
    MaximumCall625Inner40SplitFrom860From861.leaf MaximumCall625Inner40ValueFrom860From861.value
    first_lookup MaximumCall625Inner40ValueFrom860From861.value_eq) as Hfirst.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall625Leaf13ContextFrom860From861.depth (List.skipn 1 (MaximumListChunks.chunk_at 5 MaximumCall625Leaf13ContextFrom860From861.leaves)) 4
    MaximumCall625Inner45SplitFrom860From861.leaf MaximumCall625Inner45ValueFrom860From861.value
    second_lookup MaximumCall625Inner45ValueFrom860From861.value_eq) as Hsecond.
  rewrite Hfirst, Hsecond.
  rewrite MaximumCall625Leaf13Chunk05PrefixFrom860From861.values_eq, MaximumCall625Leaf13Chunk05MiddleFrom860From861.values_eq,
    MaximumCall625Leaf13Chunk05SuffixFrom860From861.values_eq.
  reflexivity.
Qed.
