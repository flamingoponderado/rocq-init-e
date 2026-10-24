From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall868Loop120Context MaximumCall868Loop120Leaf13Split MaximumCall868Loop120Leaf13Value MaximumCall868Loop120Chunk01Prefix MaximumCall868Loop120Chunk01Suffix.

Definition values :=
  MaximumCall868Loop120Chunk01Prefix.values ++ MaximumCall868Loop120Leaf13Value.value :: MaximumCall868Loop120Chunk01Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 1 MaximumCall868Loop120Context.leaves)
    5 = Some MaximumCall868Loop120Leaf13Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 1
    MaximumCall868Loop120Context.leaves) 5)). Qed.

Lemma values_eq :
  List.map MaximumCall868Loop120Context.depth
    (MaximumListChunks.chunk_at 1 MaximumCall868Loop120Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall868Loop120Chunk01Prefix.values_eq.
  rewrite <- MaximumCall868Loop120Chunk01Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall868Loop120Context.depth (MaximumListChunks.chunk_at 1 MaximumCall868Loop120Context.leaves)
    5 MaximumCall868Loop120Leaf13Split.leaf MaximumCall868Loop120Leaf13Value.value).
  - exact leaf_lookup.
  - exact MaximumCall868Loop120Leaf13Value.value_eq.
Qed.
