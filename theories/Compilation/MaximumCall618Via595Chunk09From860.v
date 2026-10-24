From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall618Via595ContextFrom860 MaximumCall618Leaf72SplitFrom860 MaximumCall618Leaf72ValueFrom860 MaximumCall618Leaf75SplitFrom860 MaximumCall618Leaf75ValueFrom860
  MaximumCall618Via595Chunk09MiddleFrom860 MaximumCall618Via595Chunk09SuffixFrom860.

Definition values :=
  MaximumCall618Leaf72ValueFrom860.value ::
  MaximumCall618Via595Chunk09MiddleFrom860.values ++ MaximumCall618Leaf75ValueFrom860.value :: MaximumCall618Via595Chunk09SuffixFrom860.values.

Lemma first_lookup : List.nth_error (MaximumListChunks.chunk_at 9 MaximumCall618Via595ContextFrom860.leaves) 0 = Some MaximumCall618Leaf72SplitFrom860.leaf.
Proof. vm_cast_no_check (eq_refl (List.nth_error (MaximumListChunks.chunk_at 9 MaximumCall618Via595ContextFrom860.leaves) 0)). Qed.

Lemma second_lookup :
  List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 9 MaximumCall618Via595ContextFrom860.leaves)) 2 = Some MaximumCall618Leaf75SplitFrom860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 9 MaximumCall618Via595ContextFrom860.leaves)) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall618Via595ContextFrom860.depth (MaximumListChunks.chunk_at 9 MaximumCall618Via595ContextFrom860.leaves) = values.
Proof.
  unfold values.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall618Via595ContextFrom860.depth (MaximumListChunks.chunk_at 9 MaximumCall618Via595ContextFrom860.leaves) 0
    MaximumCall618Leaf72SplitFrom860.leaf MaximumCall618Leaf72ValueFrom860.value
    first_lookup MaximumCall618Leaf72ValueFrom860.value_eq) as Hfirst.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall618Via595ContextFrom860.depth (List.skipn 1 (MaximumListChunks.chunk_at 9 MaximumCall618Via595ContextFrom860.leaves)) 2
    MaximumCall618Leaf75SplitFrom860.leaf MaximumCall618Leaf75ValueFrom860.value
    second_lookup MaximumCall618Leaf75ValueFrom860.value_eq) as Hsecond.
  rewrite Hfirst, Hsecond.
  rewrite MaximumCall618Via595Chunk09MiddleFrom860.values_eq, MaximumCall618Via595Chunk09SuffixFrom860.values_eq.
  cbn [List.firstn List.map List.app].
  reflexivity.
Qed.
