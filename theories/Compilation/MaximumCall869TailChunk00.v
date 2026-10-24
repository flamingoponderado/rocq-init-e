From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall869TailContext MaximumCall869Leaf224Split MaximumCall869Leaf224Value MaximumCall869TailChunk00Prefix MaximumCall869TailChunk00Suffix.

Definition values :=
  MaximumCall869TailChunk00Prefix.values ++ MaximumCall869Leaf224Value.value :: MaximumCall869TailChunk00Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 0 MaximumCall869TailContext.leaves)
    0 = Some MaximumCall869Leaf224Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 0
    MaximumCall869TailContext.leaves) 0)). Qed.

Lemma values_eq :
  List.map MaximumCall869TailContext.depth
    (MaximumListChunks.chunk_at 0 MaximumCall869TailContext.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall869TailChunk00Prefix.values_eq.
  rewrite <- MaximumCall869TailChunk00Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall869TailContext.depth (MaximumListChunks.chunk_at 0 MaximumCall869TailContext.leaves)
    0 MaximumCall869Leaf224Split.leaf MaximumCall869Leaf224Value.value).
  - exact leaf_lookup.
  - exact MaximumCall869Leaf224Value.value_eq.
Qed.
