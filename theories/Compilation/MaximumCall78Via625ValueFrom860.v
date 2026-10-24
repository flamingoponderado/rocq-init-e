From Galette Require Import Base.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall78Via625ContextFrom860 MaximumCall78Via625Chunk00From860
  MaximumCall78Via625Chunk01From860 MaximumCall78Via625Chunk02From860.

Definition values :=
  MaximumCall78Via625Chunk00From860.values ++
  MaximumCall78Via625Chunk01From860.values ++
  MaximumCall78Via625Chunk02From860.values.

Lemma values_eq :
  List.map MaximumCall78Via625ContextFrom860.depth MaximumCall78Via625ContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 3
    MaximumCall78Via625ContextFrom860.depth MaximumCall78Via625ContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall78Via625Chunk00From860.values_eq,
      MaximumCall78Via625Chunk01From860.values_eq,
      MaximumCall78Via625Chunk02From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
