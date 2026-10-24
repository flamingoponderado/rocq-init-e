From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall625Leaf13Context MaximumCall625Inner40Split MaximumCall625Inner40Value MaximumCall625Inner45Split MaximumCall625Inner45Value
  MaximumCall625Leaf13Chunk05Prefix MaximumCall625Leaf13Chunk05Middle MaximumCall625Leaf13Chunk05Suffix.

Definition values :=
  MaximumCall625Leaf13Chunk05Prefix.values ++
  (MaximumCall625Inner40Value.value ::
    (MaximumCall625Leaf13Chunk05Middle.values ++
      (MaximumCall625Inner45Value.value :: MaximumCall625Leaf13Chunk05Suffix.values))).

Lemma first_lookup : List.nth_error (MaximumListChunks.chunk_at 5 MaximumCall625Leaf13Context.leaves) 0 = Some MaximumCall625Inner40Split.leaf.
Proof. vm_cast_no_check (eq_refl (List.nth_error (MaximumListChunks.chunk_at 5 MaximumCall625Leaf13Context.leaves) 0)). Qed.

Lemma second_lookup :
  List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 5 MaximumCall625Leaf13Context.leaves)) 4 = Some MaximumCall625Inner45Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 5 MaximumCall625Leaf13Context.leaves)) 4)). Qed.

Lemma values_eq :
  List.map MaximumCall625Leaf13Context.depth (MaximumListChunks.chunk_at 5 MaximumCall625Leaf13Context.leaves) = values.
Proof.
  unfold values.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall625Leaf13Context.depth (MaximumListChunks.chunk_at 5 MaximumCall625Leaf13Context.leaves) 0
    MaximumCall625Inner40Split.leaf MaximumCall625Inner40Value.value
    first_lookup MaximumCall625Inner40Value.value_eq) as Hfirst.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall625Leaf13Context.depth (List.skipn 1 (MaximumListChunks.chunk_at 5 MaximumCall625Leaf13Context.leaves)) 4
    MaximumCall625Inner45Split.leaf MaximumCall625Inner45Value.value
    second_lookup MaximumCall625Inner45Value.value_eq) as Hsecond.
  rewrite Hfirst, Hsecond.
  rewrite MaximumCall625Leaf13Chunk05Prefix.values_eq, MaximumCall625Leaf13Chunk05Middle.values_eq,
    MaximumCall625Leaf13Chunk05Suffix.values_eq.
  reflexivity.
Qed.
