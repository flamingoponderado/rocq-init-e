From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall618Via595ContextFrom608 MaximumCall618Leaf72SplitFrom608 MaximumCall618Leaf72ValueFrom608 MaximumCall618Leaf75SplitFrom608 MaximumCall618Leaf75ValueFrom608
  MaximumCall618Via595Chunk09MiddleFrom608 MaximumCall618Via595Chunk09SuffixFrom608.

Definition values :=
  MaximumCall618Leaf72ValueFrom608.value ::
  MaximumCall618Via595Chunk09MiddleFrom608.values ++ MaximumCall618Leaf75ValueFrom608.value :: MaximumCall618Via595Chunk09SuffixFrom608.values.

Lemma first_lookup : List.nth_error (MaximumListChunks.chunk_at 9 MaximumCall618Via595ContextFrom608.leaves) 0 = Some MaximumCall618Leaf72SplitFrom608.leaf.
Proof. vm_cast_no_check (eq_refl (List.nth_error (MaximumListChunks.chunk_at 9 MaximumCall618Via595ContextFrom608.leaves) 0)). Qed.

Lemma second_lookup :
  List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 9 MaximumCall618Via595ContextFrom608.leaves)) 2 = Some MaximumCall618Leaf75SplitFrom608.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 9 MaximumCall618Via595ContextFrom608.leaves)) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall618Via595ContextFrom608.depth (MaximumListChunks.chunk_at 9 MaximumCall618Via595ContextFrom608.leaves) = values.
Proof.
  unfold values.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall618Via595ContextFrom608.depth (MaximumListChunks.chunk_at 9 MaximumCall618Via595ContextFrom608.leaves) 0
    MaximumCall618Leaf72SplitFrom608.leaf MaximumCall618Leaf72ValueFrom608.value
    first_lookup MaximumCall618Leaf72ValueFrom608.value_eq) as Hfirst.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall618Via595ContextFrom608.depth (List.skipn 1 (MaximumListChunks.chunk_at 9 MaximumCall618Via595ContextFrom608.leaves)) 2
    MaximumCall618Leaf75SplitFrom608.leaf MaximumCall618Leaf75ValueFrom608.value
    second_lookup MaximumCall618Leaf75ValueFrom608.value_eq) as Hsecond.
  rewrite Hfirst, Hsecond.
  rewrite MaximumCall618Via595Chunk09MiddleFrom608.values_eq, MaximumCall618Via595Chunk09SuffixFrom608.values_eq.
  cbn [List.firstn List.map List.app].
  reflexivity.
Qed.
