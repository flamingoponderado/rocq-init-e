From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall863Via868Context MaximumCall863Leaf367Split MaximumCall863Leaf367Value MaximumCall863Via868Chunk45Prefix MaximumCall863Via868Chunk45Suffix.

Definition values :=
  MaximumCall863Via868Chunk45Prefix.values ++ MaximumCall863Leaf367Value.value :: MaximumCall863Via868Chunk45Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 45 MaximumCall863Via868Context.leaves)
    7 = Some MaximumCall863Leaf367Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 45
    MaximumCall863Via868Context.leaves) 7)). Qed.

Lemma values_eq :
  List.map MaximumCall863Via868Context.depth
    (MaximumListChunks.chunk_at 45 MaximumCall863Via868Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall863Via868Chunk45Prefix.values_eq.
  rewrite <- MaximumCall863Via868Chunk45Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall863Via868Context.depth (MaximumListChunks.chunk_at 45 MaximumCall863Via868Context.leaves)
    7 MaximumCall863Leaf367Split.leaf MaximumCall863Leaf367Value.value).
  - exact leaf_lookup.
  - exact MaximumCall863Leaf367Value.value_eq.
Qed.
