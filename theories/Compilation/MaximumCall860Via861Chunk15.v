From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall860Via861Context MaximumCall860Leaf126SplitFrom861 MaximumCall860Leaf126ValueFrom861 MaximumCall860Via861Chunk15Prefix MaximumCall860Via861Chunk15Suffix.

Definition values :=
  MaximumCall860Via861Chunk15Prefix.values ++ MaximumCall860Leaf126ValueFrom861.value :: MaximumCall860Via861Chunk15Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 15 MaximumCall860Via861Context.leaves)
    6 = Some MaximumCall860Leaf126SplitFrom861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 15
    MaximumCall860Via861Context.leaves) 6)). Qed.

Lemma values_eq :
  List.map MaximumCall860Via861Context.depth
    (MaximumListChunks.chunk_at 15 MaximumCall860Via861Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall860Via861Chunk15Prefix.values_eq.
  rewrite <- MaximumCall860Via861Chunk15Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall860Via861Context.depth (MaximumListChunks.chunk_at 15 MaximumCall860Via861Context.leaves)
    6 MaximumCall860Leaf126SplitFrom861.leaf MaximumCall860Leaf126ValueFrom861.value).
  - exact leaf_lookup.
  - exact MaximumCall860Leaf126ValueFrom861.value_eq.
Qed.
