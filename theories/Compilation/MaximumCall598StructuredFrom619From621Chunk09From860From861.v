From Galette Require Import Base.
From Stdlib Require Import List.
From Galette.cakeml.compiler.backend Require Import wordLang.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall598StructuredFrom619From621ContextFrom860From861
  MaximumCall598From619From621Leaf77SplitFrom860From861
  MaximumCall598From619From621Leaf77ValueFrom860From861
  MaximumCall598StructuredFrom619From621Chunk09PrefixFrom860From861
  MaximumCall598StructuredFrom619From621Chunk09SuffixFrom860From861.

Definition values :=
  MaximumCall598StructuredFrom619From621Chunk09PrefixFrom860From861.values ++
  MaximumCall598From619From621Leaf77ValueFrom860From861.value ::
  MaximumCall598StructuredFrom619From621Chunk09SuffixFrom860From861.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 9
    MaximumCall598StructuredFrom619From621ContextFrom860From861.leaves) 5 =
  Some MaximumCall598From619From621Leaf77SplitFrom860From861.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 9
    MaximumCall598StructuredFrom619From621ContextFrom860From861.leaves) 5)). Qed.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom619From621ContextFrom860From861.depth
    (MaximumListChunks.chunk_at 9
      MaximumCall598StructuredFrom619From621ContextFrom860From861.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall598StructuredFrom619From621Chunk09PrefixFrom860From861.values_eq.
  rewrite <- MaximumCall598StructuredFrom619From621Chunk09SuffixFrom860From861.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall598StructuredFrom619From621ContextFrom860From861.depth
    (MaximumListChunks.chunk_at 9
      MaximumCall598StructuredFrom619From621ContextFrom860From861.leaves)
    5 MaximumCall598From619From621Leaf77SplitFrom860From861.leaf
    MaximumCall598From619From621Leaf77ValueFrom860From861.value).
  - exact leaf_lookup.
  - exact MaximumCall598From619From621Leaf77ValueFrom860From861.value_eq.
Qed.
