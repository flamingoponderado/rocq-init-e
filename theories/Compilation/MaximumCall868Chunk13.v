From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall868SuffixContext MaximumCall868SuffixLeaf106Split MaximumCall868SuffixLeaf106Value MaximumCall868SuffixLeaf109Split MaximumCall868SuffixLeaf109Value
  MaximumCall868Chunk13Prefix MaximumCall868Chunk13Middle MaximumCall868Chunk13Suffix.

Definition values :=
  MaximumCall868Chunk13Prefix.values ++
  (MaximumCall868SuffixLeaf106Value.value ::
    (MaximumCall868Chunk13Middle.values ++
      (MaximumCall868SuffixLeaf109Value.value :: MaximumCall868Chunk13Suffix.values))).

Lemma first_lookup : List.nth_error (MaximumListChunks.chunk_at 13 MaximumCall868SuffixContext.leaves) 2 = Some MaximumCall868SuffixLeaf106Split.leaf.
Proof. vm_cast_no_check (eq_refl (List.nth_error (MaximumListChunks.chunk_at 13 MaximumCall868SuffixContext.leaves) 2)). Qed.

Lemma second_lookup :
  List.nth_error (List.skipn 3 (MaximumListChunks.chunk_at 13 MaximumCall868SuffixContext.leaves)) 2 = Some MaximumCall868SuffixLeaf109Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (List.skipn 3 (MaximumListChunks.chunk_at 13 MaximumCall868SuffixContext.leaves)) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall868SuffixContext.depth (MaximumListChunks.chunk_at 13 MaximumCall868SuffixContext.leaves) = values.
Proof.
  unfold values.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall868SuffixContext.depth (MaximumListChunks.chunk_at 13 MaximumCall868SuffixContext.leaves) 2
    MaximumCall868SuffixLeaf106Split.leaf MaximumCall868SuffixLeaf106Value.value
    first_lookup MaximumCall868SuffixLeaf106Value.value_eq) as Hfirst.
  pose proof (MaximumListChunks.map_replace_middle
    MaximumCall868SuffixContext.depth (List.skipn 3 (MaximumListChunks.chunk_at 13 MaximumCall868SuffixContext.leaves)) 2
    MaximumCall868SuffixLeaf109Split.leaf MaximumCall868SuffixLeaf109Value.value
    second_lookup MaximumCall868SuffixLeaf109Value.value_eq) as Hsecond.
  rewrite Hfirst, Hsecond.
  rewrite MaximumCall868Chunk13Prefix.values_eq, MaximumCall868Chunk13Middle.values_eq,
    MaximumCall868Chunk13Suffix.values_eq.
  reflexivity.
Qed.

From InitE.Compilation Require Import MaximumCall868Context MaximumCall868Pieces.
Lemma values_eq_old :
  List.map MaximumCall868Context.depth
    (MaximumListChunks.chunk_at 13 MaximumCall868Pieces.suffix) = values.
Proof. exact values_eq. Qed.
