From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall603Via619From621Context MaximumCall603From619From621Leaf61Split MaximumCall603From619From621Leaf61Value MaximumCall603Via619From621Chunk07Prefix MaximumCall603Via619From621Chunk07Suffix.

Definition values :=
  MaximumCall603Via619From621Chunk07Prefix.values ++ MaximumCall603From619From621Leaf61Value.value :: MaximumCall603Via619From621Chunk07Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 7 MaximumCall603Via619From621Context.leaves)
    5 = Some MaximumCall603From619From621Leaf61Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 7
    MaximumCall603Via619From621Context.leaves) 5)). Qed.

Lemma values_eq :
  List.map MaximumCall603Via619From621Context.depth
    (MaximumListChunks.chunk_at 7 MaximumCall603Via619From621Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall603Via619From621Chunk07Prefix.values_eq.
  rewrite <- MaximumCall603Via619From621Chunk07Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall603Via619From621Context.depth (MaximumListChunks.chunk_at 7 MaximumCall603Via619From621Context.leaves)
    5 MaximumCall603From619From621Leaf61Split.leaf MaximumCall603From619From621Leaf61Value.value).
  - exact leaf_lookup.
  - exact MaximumCall603From619From621Leaf61Value.value_eq.
Qed.
