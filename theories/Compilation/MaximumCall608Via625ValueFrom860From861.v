From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall608Via625ContextFrom860From861 MaximumCall608Via625Chunk00From860From861 MaximumCall608Via625Chunk01From860From861 MaximumCall608Via625Chunk02From860From861 MaximumCall608Via625Chunk03From860From861.

Definition values :=
  MaximumCall608Via625Chunk00From860From861.values ++
  MaximumCall608Via625Chunk01From860From861.values ++
  MaximumCall608Via625Chunk02From860From861.values ++
  MaximumCall608Via625Chunk03From860From861.values.

Lemma values_eq :
  List.map MaximumCall608Via625ContextFrom860From861.depth MaximumCall608Via625ContextFrom860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 4
    MaximumCall608Via625ContextFrom860From861.depth MaximumCall608Via625ContextFrom860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall608Via625Chunk00From860From861.values_eq,
      MaximumCall608Via625Chunk01From860From861.values_eq,
      MaximumCall608Via625Chunk02From860From861.values_eq,
      MaximumCall608Via625Chunk03From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
