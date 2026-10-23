From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall617Via595Context MaximumCall617Leaf59Split MaximumCall617Leaf59Value MaximumCall617Via595Chunk07Prefix MaximumCall617Via595Chunk07Suffix.

Definition values :=
  MaximumCall617Via595Chunk07Prefix.values ++ MaximumCall617Leaf59Value.value :: MaximumCall617Via595Chunk07Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 7 MaximumCall617Via595Context.leaves)
    3 = Some MaximumCall617Leaf59Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 7
    MaximumCall617Via595Context.leaves) 3)). Qed.

Lemma values_eq :
  List.map MaximumCall617Via595Context.depth
    (MaximumListChunks.chunk_at 7 MaximumCall617Via595Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall617Via595Chunk07Prefix.values_eq.
  rewrite <- MaximumCall617Via595Chunk07Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall617Via595Context.depth (MaximumListChunks.chunk_at 7 MaximumCall617Via595Context.leaves)
    3 MaximumCall617Leaf59Split.leaf MaximumCall617Leaf59Value.value).
  - exact leaf_lookup.
  - exact MaximumCall617Leaf59Value.value_eq.
Qed.
