From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall625Via860Context MaximumCall625Leaf08SplitFrom860 MaximumCall625Leaf08ValueFrom860 MaximumCall625Leaf13AliasFrom860 MaximumCall625Leaf13OuterValueFrom860
  MaximumCall625Via860Chunk01Prefix MaximumCall625Via860Chunk01Middle MaximumCall625Via860Chunk01Suffix.

Definition values :=
  MaximumCall625Via860Chunk01Prefix.values ++
  (MaximumCall625Leaf08ValueFrom860.value ::
    (MaximumCall625Via860Chunk01Middle.values ++
      (MaximumCall625Leaf13OuterValueFrom860.value :: MaximumCall625Via860Chunk01Suffix.values))).

Lemma first_lookup : List.nth_error (MaximumListChunks.chunk_at 1 MaximumCall625Via860Context.leaves) 0 = Some MaximumCall625Leaf08SplitFrom860.leaf.
Proof. vm_cast_no_check (eq_refl (List.nth_error (MaximumListChunks.chunk_at 1 MaximumCall625Via860Context.leaves) 0)). Qed.

Lemma second_lookup :
  List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 1 MaximumCall625Via860Context.leaves)) 4 = Some MaximumCall625Leaf13AliasFrom860.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (List.skipn 1 (MaximumListChunks.chunk_at 1 MaximumCall625Via860Context.leaves)) 4)). Qed.

Lemma values_eq :
  List.map MaximumCall625Via860Context.depth (MaximumListChunks.chunk_at 1 MaximumCall625Via860Context.leaves) = values.
Proof.
  unfold values.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall625Via860Context.depth (MaximumListChunks.chunk_at 1 MaximumCall625Via860Context.leaves) 0
    MaximumCall625Leaf08SplitFrom860.leaf MaximumCall625Leaf08ValueFrom860.value
    first_lookup MaximumCall625Leaf08ValueFrom860.value_eq) as Hfirst.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall625Via860Context.depth (List.skipn 1 (MaximumListChunks.chunk_at 1 MaximumCall625Via860Context.leaves)) 4
    MaximumCall625Leaf13AliasFrom860.leaf MaximumCall625Leaf13OuterValueFrom860.value
    second_lookup MaximumCall625Leaf13OuterValueFrom860.value_eq) as Hsecond.
  rewrite Hfirst, Hsecond.
  rewrite MaximumCall625Via860Chunk01Prefix.values_eq, MaximumCall625Via860Chunk01Middle.values_eq,
    MaximumCall625Via860Chunk01Suffix.values_eq.
  reflexivity.
Qed.
