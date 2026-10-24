From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall606Via608Context MaximumCall606Leaf34SplitFrom608 MaximumCall606Leaf34ValueFrom608 MaximumCall606Leaf37SplitFrom608 MaximumCall606Leaf37ValueFrom608
  MaximumCall606Via608Chunk04Prefix MaximumCall606Via608Chunk04Middle MaximumCall606Via608Chunk04Suffix.

Definition values :=
  MaximumCall606Via608Chunk04Prefix.values ++
  (MaximumCall606Leaf34ValueFrom608.value ::
    (MaximumCall606Via608Chunk04Middle.values ++
      (MaximumCall606Leaf37ValueFrom608.value :: MaximumCall606Via608Chunk04Suffix.values))).

Lemma first_lookup : List.nth_error (MaximumListChunks.chunk_at 4 MaximumCall606Via608Context.leaves) 2 = Some MaximumCall606Leaf34SplitFrom608.leaf.
Proof. vm_cast_no_check (eq_refl (List.nth_error (MaximumListChunks.chunk_at 4 MaximumCall606Via608Context.leaves) 2)). Qed.

Lemma second_lookup :
  List.nth_error (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via608Context.leaves)) 2 = Some MaximumCall606Leaf37SplitFrom608.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via608Context.leaves)) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall606Via608Context.depth (MaximumListChunks.chunk_at 4 MaximumCall606Via608Context.leaves) = values.
Proof.
  unfold values.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall606Via608Context.depth (MaximumListChunks.chunk_at 4 MaximumCall606Via608Context.leaves) 2
    MaximumCall606Leaf34SplitFrom608.leaf MaximumCall606Leaf34ValueFrom608.value
    first_lookup MaximumCall606Leaf34ValueFrom608.value_eq) as Hfirst.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall606Via608Context.depth (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via608Context.leaves)) 2
    MaximumCall606Leaf37SplitFrom608.leaf MaximumCall606Leaf37ValueFrom608.value
    second_lookup MaximumCall606Leaf37ValueFrom608.value_eq) as Hsecond.
  rewrite Hfirst, Hsecond.
  rewrite MaximumCall606Via608Chunk04Prefix.values_eq, MaximumCall606Via608Chunk04Middle.values_eq,
    MaximumCall606Via608Chunk04Suffix.values_eq.
  reflexivity.
Qed.
