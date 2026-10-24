From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall608Via625ContextFrom860 MaximumCall608Via625Chunk00From860 MaximumCall608Via625Chunk01From860 MaximumCall608Via625Chunk02From860 MaximumCall608Via625Chunk03From860.

Definition values :=
  MaximumCall608Via625Chunk00From860.values ++
  MaximumCall608Via625Chunk01From860.values ++
  MaximumCall608Via625Chunk02From860.values ++
  MaximumCall608Via625Chunk03From860.values.

Lemma values_eq :
  List.map MaximumCall608Via625ContextFrom860.depth MaximumCall608Via625ContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 4
    MaximumCall608Via625ContextFrom860.depth MaximumCall608Via625ContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall608Via625Chunk00From860.values_eq,
      MaximumCall608Via625Chunk01From860.values_eq,
      MaximumCall608Via625Chunk02From860.values_eq,
      MaximumCall608Via625Chunk03From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
