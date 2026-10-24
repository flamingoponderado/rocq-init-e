From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall860Via868Context MaximumCall860Leaf126Split MaximumCall860Leaf126Value MaximumCall860Via868Chunk15Prefix MaximumCall860Via868Chunk15Suffix.

Definition values :=
  MaximumCall860Via868Chunk15Prefix.values ++ MaximumCall860Leaf126Value.value :: MaximumCall860Via868Chunk15Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 15 MaximumCall860Via868Context.leaves)
    6 = Some MaximumCall860Leaf126Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 15
    MaximumCall860Via868Context.leaves) 6)). Qed.

Lemma values_eq :
  List.map MaximumCall860Via868Context.depth
    (MaximumListChunks.chunk_at 15 MaximumCall860Via868Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall860Via868Chunk15Prefix.values_eq.
  rewrite <- MaximumCall860Via868Chunk15Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall860Via868Context.depth (MaximumListChunks.chunk_at 15 MaximumCall860Via868Context.leaves)
    6 MaximumCall860Leaf126Split.leaf MaximumCall860Leaf126Value.value).
  - exact leaf_lookup.
  - exact MaximumCall860Leaf126Value.value_eq.
Qed.
