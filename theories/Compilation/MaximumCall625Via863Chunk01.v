From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall625Via863Context MaximumCall625Leaf08Split MaximumCall625Leaf08Value MaximumCall625Leaf13Alias MaximumCall625Leaf13OuterValue
  MaximumCall625Via863Chunk01Prefix MaximumCall625Via863Chunk01Middle MaximumCall625Via863Chunk01Suffix.

Definition values :=
  MaximumCall625Via863Chunk01Prefix.values ++
  (MaximumCall625Leaf08Value.value ::
    (MaximumCall625Via863Chunk01Middle.values ++
      (MaximumCall625Leaf13OuterValue.value :: MaximumCall625Via863Chunk01Suffix.values))).

Lemma first_lookup : List.nth_error (MaximumListChunks.chunk_at 1 MaximumCall625Via863Context.leaves) 0 = Some MaximumCall625Leaf08Split.leaf.
Proof. vm_cast_no_check (eq_refl (List.nth_error (MaximumListChunks.chunk_at 1 MaximumCall625Via863Context.leaves) 0)). Qed.

Lemma second_lookup :
  List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 1 MaximumCall625Via863Context.leaves)) 4 = Some MaximumCall625Leaf13Alias.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 1 MaximumCall625Via863Context.leaves)) 4)). Qed.

Lemma values_eq :
  List.map MaximumCall625Via863Context.depth (MaximumListChunks.chunk_at 1 MaximumCall625Via863Context.leaves) = values.
Proof.
  unfold values.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall625Via863Context.depth (MaximumListChunks.chunk_at 1 MaximumCall625Via863Context.leaves) 0
    MaximumCall625Leaf08Split.leaf MaximumCall625Leaf08Value.value
    first_lookup MaximumCall625Leaf08Value.value_eq) as Hfirst.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall625Via863Context.depth (List.skipn 1 (MaximumListChunks.chunk_at 1 MaximumCall625Via863Context.leaves)) 4
    MaximumCall625Leaf13Alias.leaf MaximumCall625Leaf13OuterValue.value
    second_lookup MaximumCall625Leaf13OuterValue.value_eq) as Hsecond.
  rewrite Hfirst, Hsecond.
  rewrite MaximumCall625Via863Chunk01Prefix.values_eq, MaximumCall625Via863Chunk01Middle.values_eq,
    MaximumCall625Via863Chunk01Suffix.values_eq.
  reflexivity.
Qed.
