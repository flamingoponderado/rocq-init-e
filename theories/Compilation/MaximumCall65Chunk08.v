From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall65Context MaximumCall65Leaf66Split MaximumCall65Leaf66Value MaximumCall65Chunk08Prefix MaximumCall65Chunk08Suffix.

Definition values :=
  MaximumCall65Chunk08Prefix.values ++ MaximumCall65Leaf66Value.value :: MaximumCall65Chunk08Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 8 MaximumCall65Context.leaves)
    2 = Some MaximumCall65Leaf66Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 8
    MaximumCall65Context.leaves) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall65Context.depth
    (MaximumListChunks.chunk_at 8 MaximumCall65Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall65Chunk08Prefix.values_eq.
  rewrite <- MaximumCall65Chunk08Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall65Context.depth (MaximumListChunks.chunk_at 8 MaximumCall65Context.leaves)
    2 MaximumCall65Leaf66Split.leaf MaximumCall65Leaf66Value.value).
  - exact leaf_lookup.
  - exact MaximumCall65Leaf66Value.value_eq.
Qed.
