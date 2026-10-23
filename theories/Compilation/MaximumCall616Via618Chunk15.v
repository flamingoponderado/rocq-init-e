From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall616Via618Context MaximumCall616From618Leaf124Split MaximumCall616From618Leaf124Value MaximumCall616Via618Chunk15Prefix MaximumCall616Via618Chunk15Suffix.

Definition values :=
  MaximumCall616Via618Chunk15Prefix.values ++ MaximumCall616From618Leaf124Value.value :: MaximumCall616Via618Chunk15Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 15 MaximumCall616Via618Context.leaves)
    4 = Some MaximumCall616From618Leaf124Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 15
    MaximumCall616Via618Context.leaves) 4)). Qed.

Lemma values_eq :
  List.map MaximumCall616Via618Context.depth
    (MaximumListChunks.chunk_at 15 MaximumCall616Via618Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall616Via618Chunk15Prefix.values_eq.
  rewrite <- MaximumCall616Via618Chunk15Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall616Via618Context.depth (MaximumListChunks.chunk_at 15 MaximumCall616Via618Context.leaves)
    4 MaximumCall616From618Leaf124Split.leaf MaximumCall616From618Leaf124Value.value).
  - exact leaf_lookup.
  - exact MaximumCall616From618Leaf124Value.value_eq.
Qed.
