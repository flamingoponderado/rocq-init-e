From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall868SuffixContext MaximumCall868SuffixLeaf90Split MaximumCall868SuffixLeaf90Value MaximumCall868Chunk11Prefix MaximumCall868Chunk11Suffix.

Definition values :=
  MaximumCall868Chunk11Prefix.values ++ MaximumCall868SuffixLeaf90Value.value :: MaximumCall868Chunk11Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 11 MaximumCall868SuffixContext.leaves)
    2 = Some MaximumCall868SuffixLeaf90Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 11
    MaximumCall868SuffixContext.leaves) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall868SuffixContext.depth
    (MaximumListChunks.chunk_at 11 MaximumCall868SuffixContext.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall868Chunk11Prefix.values_eq.
  rewrite <- MaximumCall868Chunk11Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall868SuffixContext.depth (MaximumListChunks.chunk_at 11 MaximumCall868SuffixContext.leaves)
    2 MaximumCall868SuffixLeaf90Split.leaf MaximumCall868SuffixLeaf90Value.value).
  - exact leaf_lookup.
  - exact MaximumCall868SuffixLeaf90Value.value_eq.
Qed.

From InitE.Compilation Require Import MaximumCall868Context MaximumCall868Pieces.
Lemma values_eq_old :
  List.map MaximumCall868Context.depth
    (MaximumListChunks.chunk_at 11 MaximumCall868Pieces.suffix) = values.
Proof. exact values_eq. Qed.
