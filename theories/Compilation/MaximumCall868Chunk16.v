From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall868SuffixContext MaximumCall868SuffixLeaf131Split MaximumCall868SuffixLeaf131Value MaximumCall868SuffixLeaf134Split MaximumCall868SuffixLeaf134Value
  MaximumCall868Chunk16Prefix MaximumCall868Chunk16Middle MaximumCall868Chunk16Suffix.

Definition values :=
  MaximumCall868Chunk16Prefix.values ++
  (MaximumCall868SuffixLeaf131Value.value ::
    (MaximumCall868Chunk16Middle.values ++
      (MaximumCall868SuffixLeaf134Value.value :: MaximumCall868Chunk16Suffix.values))).

Lemma first_lookup : List.nth_error (MaximumListChunks.chunk_at 16 MaximumCall868SuffixContext.leaves) 3 = Some MaximumCall868SuffixLeaf131Split.leaf.
Proof. vm_cast_no_check (eq_refl (List.nth_error (MaximumListChunks.chunk_at 16 MaximumCall868SuffixContext.leaves) 3)). Qed.

Lemma second_lookup :
  List.nth_error (List.skipn 4 (MaximumListChunks.chunk_at 16 MaximumCall868SuffixContext.leaves)) 2 = Some MaximumCall868SuffixLeaf134Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (List.skipn 4 (MaximumListChunks.chunk_at 16 MaximumCall868SuffixContext.leaves)) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall868SuffixContext.depth (MaximumListChunks.chunk_at 16 MaximumCall868SuffixContext.leaves) = values.
Proof.
  unfold values.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall868SuffixContext.depth (MaximumListChunks.chunk_at 16 MaximumCall868SuffixContext.leaves) 3
    MaximumCall868SuffixLeaf131Split.leaf MaximumCall868SuffixLeaf131Value.value
    first_lookup MaximumCall868SuffixLeaf131Value.value_eq) as Hfirst.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall868SuffixContext.depth (List.skipn 4 (MaximumListChunks.chunk_at 16 MaximumCall868SuffixContext.leaves)) 2
    MaximumCall868SuffixLeaf134Split.leaf MaximumCall868SuffixLeaf134Value.value
    second_lookup MaximumCall868SuffixLeaf134Value.value_eq) as Hsecond.
  rewrite Hfirst, Hsecond.
  rewrite MaximumCall868Chunk16Prefix.values_eq, MaximumCall868Chunk16Middle.values_eq,
    MaximumCall868Chunk16Suffix.values_eq.
  reflexivity.
Qed.

From InitE.Compilation Require Import MaximumCall868Context MaximumCall868Pieces.
Lemma values_eq_old :
  List.map MaximumCall868Context.depth
    (MaximumListChunks.chunk_at 16 MaximumCall868Pieces.suffix) = values.
Proof. exact values_eq. Qed.
