From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall616Via617Context MaximumCall616From617Leaf131Split MaximumCall616From617Leaf131Value MaximumCall616Via617Chunk16Prefix MaximumCall616Via617Chunk16Suffix.

Definition values :=
  MaximumCall616Via617Chunk16Prefix.values ++ MaximumCall616From617Leaf131Value.value :: MaximumCall616Via617Chunk16Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 16 MaximumCall616Via617Context.leaves)
    3 = Some MaximumCall616From617Leaf131Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 16
    MaximumCall616Via617Context.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall616Via617Context.depth
    (MaximumListChunks.chunk_at 16 MaximumCall616Via617Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall616Via617Chunk16Prefix.values_eq.
  rewrite <- MaximumCall616Via617Chunk16Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall616Via617Context.depth (MaximumListChunks.chunk_at 16 MaximumCall616Via617Context.leaves)
    3 MaximumCall616From617Leaf131Split.leaf MaximumCall616From617Leaf131Value.value).
  - exact leaf_lookup.
  - exact MaximumCall616From617Leaf131Value.value_eq.
Qed.
