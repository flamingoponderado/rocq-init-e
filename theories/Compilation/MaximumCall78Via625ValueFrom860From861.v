From Galette Require Import Base.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall78Via625ContextFrom860From861 MaximumCall78Via625Chunk00From860From861
  MaximumCall78Via625Chunk01From860From861 MaximumCall78Via625Chunk02From860From861.

Definition values :=
  MaximumCall78Via625Chunk00From860From861.values ++
  MaximumCall78Via625Chunk01From860From861.values ++
  MaximumCall78Via625Chunk02From860From861.values.

Lemma values_eq :
  List.map MaximumCall78Via625ContextFrom860From861.depth MaximumCall78Via625ContextFrom860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 3
    MaximumCall78Via625ContextFrom860From861.depth MaximumCall78Via625ContextFrom860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall78Via625Chunk00From860From861.values_eq,
      MaximumCall78Via625Chunk01From860From861.values_eq,
      MaximumCall78Via625Chunk02From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
