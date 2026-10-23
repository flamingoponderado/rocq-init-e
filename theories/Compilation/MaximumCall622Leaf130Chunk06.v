From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall622Leaf130Context MaximumCall622Inner54Split MaximumCall622Inner54Value MaximumCall622Leaf130Chunk06Prefix MaximumCall622Leaf130Chunk06Suffix.

Definition values :=
  MaximumCall622Leaf130Chunk06Prefix.values ++ MaximumCall622Inner54Value.value :: MaximumCall622Leaf130Chunk06Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 6 MaximumCall622Leaf130Context.leaves)
    6 = Some MaximumCall622Inner54Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 6
    MaximumCall622Leaf130Context.leaves) 6)). Qed.

Lemma values_eq :
  List.map MaximumCall622Leaf130Context.depth
    (MaximumListChunks.chunk_at 6 MaximumCall622Leaf130Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall622Leaf130Chunk06Prefix.values_eq.
  rewrite <- MaximumCall622Leaf130Chunk06Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall622Leaf130Context.depth (MaximumListChunks.chunk_at 6 MaximumCall622Leaf130Context.leaves)
    6 MaximumCall622Inner54Split.leaf MaximumCall622Inner54Value.value).
  - exact leaf_lookup.
  - exact MaximumCall622Inner54Value.value_eq.
Qed.
