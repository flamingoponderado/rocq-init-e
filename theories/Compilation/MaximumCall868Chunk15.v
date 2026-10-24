From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall868SuffixContext MaximumCall868Loop120Alias MaximumCall868Loop120OuterValue MaximumCall868Chunk15Prefix MaximumCall868Chunk15Suffix.

Definition values :=
  MaximumCall868Chunk15Prefix.values ++ MaximumCall868Loop120OuterValue.value :: MaximumCall868Chunk15Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 15 MaximumCall868SuffixContext.leaves)
    0 = Some MaximumCall868Loop120Alias.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 15
    MaximumCall868SuffixContext.leaves) 0)). Qed.

Lemma values_eq :
  List.map MaximumCall868SuffixContext.depth
    (MaximumListChunks.chunk_at 15 MaximumCall868SuffixContext.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall868Chunk15Prefix.values_eq.
  rewrite <- MaximumCall868Chunk15Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall868SuffixContext.depth (MaximumListChunks.chunk_at 15 MaximumCall868SuffixContext.leaves)
    0 MaximumCall868Loop120Alias.leaf MaximumCall868Loop120OuterValue.value).
  - exact leaf_lookup.
  - exact MaximumCall868Loop120OuterValue.value_eq.
Qed.

From InitE.Compilation Require Import MaximumCall868Context MaximumCall868Pieces.
Lemma values_eq_old :
  List.map MaximumCall868Context.depth
    (MaximumListChunks.chunk_at 15 MaximumCall868Pieces.suffix) = values.
Proof. exact values_eq. Qed.
