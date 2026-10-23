From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall618Via595Context MaximumCall618Leaf72Split MaximumCall618Leaf72Value MaximumCall618Leaf75Split MaximumCall618Leaf75Value
  MaximumCall618Via595Chunk09Middle MaximumCall618Via595Chunk09Suffix.

Definition values :=
  MaximumCall618Leaf72Value.value ::
  MaximumCall618Via595Chunk09Middle.values ++ MaximumCall618Leaf75Value.value :: MaximumCall618Via595Chunk09Suffix.values.

Lemma first_lookup : List.nth_error (MaximumListChunks.chunk_at 9 MaximumCall618Via595Context.leaves) 0 = Some MaximumCall618Leaf72Split.leaf.
Proof. vm_cast_no_check (eq_refl (List.nth_error (MaximumListChunks.chunk_at 9 MaximumCall618Via595Context.leaves) 0)). Qed.

Lemma second_lookup :
  List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 9 MaximumCall618Via595Context.leaves)) 2 = Some MaximumCall618Leaf75Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 9 MaximumCall618Via595Context.leaves)) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall618Via595Context.depth (MaximumListChunks.chunk_at 9 MaximumCall618Via595Context.leaves) = values.
Proof.
  unfold values.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall618Via595Context.depth (MaximumListChunks.chunk_at 9 MaximumCall618Via595Context.leaves) 0
    MaximumCall618Leaf72Split.leaf MaximumCall618Leaf72Value.value
    first_lookup MaximumCall618Leaf72Value.value_eq) as Hfirst.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall618Via595Context.depth (List.skipn 1 (MaximumListChunks.chunk_at 9 MaximumCall618Via595Context.leaves)) 2
    MaximumCall618Leaf75Split.leaf MaximumCall618Leaf75Value.value
    second_lookup MaximumCall618Leaf75Value.value_eq) as Hsecond.
  rewrite Hfirst, Hsecond.
  rewrite MaximumCall618Via595Chunk09Middle.values_eq, MaximumCall618Via595Chunk09Suffix.values_eq.
  cbn [List.firstn List.map List.app].
  reflexivity.
Qed.
