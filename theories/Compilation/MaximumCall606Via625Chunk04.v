From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall606Via625Context MaximumCall606Leaf34Split MaximumCall606Leaf34Value MaximumCall606Leaf37Split MaximumCall606Leaf37Value
  MaximumCall606Via625Chunk04Prefix MaximumCall606Via625Chunk04Middle MaximumCall606Via625Chunk04Suffix.

Definition values :=
  MaximumCall606Via625Chunk04Prefix.values ++
  (MaximumCall606Leaf34Value.value ::
    (MaximumCall606Via625Chunk04Middle.values ++
      (MaximumCall606Leaf37Value.value :: MaximumCall606Via625Chunk04Suffix.values))).

Lemma first_lookup : List.nth_error (MaximumListChunks.chunk_at 4 MaximumCall606Via625Context.leaves) 2 = Some MaximumCall606Leaf34Split.leaf.
Proof. vm_cast_no_check (eq_refl (List.nth_error (MaximumListChunks.chunk_at 4 MaximumCall606Via625Context.leaves) 2)). Qed.

Lemma second_lookup :
  List.nth_error (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via625Context.leaves)) 2 = Some MaximumCall606Leaf37Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via625Context.leaves)) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall606Via625Context.depth (MaximumListChunks.chunk_at 4 MaximumCall606Via625Context.leaves) = values.
Proof.
  unfold values.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall606Via625Context.depth (MaximumListChunks.chunk_at 4 MaximumCall606Via625Context.leaves) 2
    MaximumCall606Leaf34Split.leaf MaximumCall606Leaf34Value.value
    first_lookup MaximumCall606Leaf34Value.value_eq) as Hfirst.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall606Via625Context.depth (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via625Context.leaves)) 2
    MaximumCall606Leaf37Split.leaf MaximumCall606Leaf37Value.value
    second_lookup MaximumCall606Leaf37Value.value_eq) as Hsecond.
  rewrite Hfirst, Hsecond.
  rewrite MaximumCall606Via625Chunk04Prefix.values_eq, MaximumCall606Via625Chunk04Middle.values_eq,
    MaximumCall606Via625Chunk04Suffix.values_eq.
  reflexivity.
Qed.
