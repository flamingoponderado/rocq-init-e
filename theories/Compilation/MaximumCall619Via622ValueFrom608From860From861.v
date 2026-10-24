From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall619Via622ContextFrom608From860From861 MaximumCall619Via622Chunk00From608From860From861 MaximumCall619Via622Chunk01From608From860From861 MaximumCall619Via622Chunk02From608From860From861 MaximumCall619Via622Chunk03From608From860From861 MaximumCall619Via622Chunk04From608From860From861 MaximumCall619Via622Chunk05From608From860From861.

Definition values :=
  MaximumCall619Via622Chunk00From608From860From861.values ++
  MaximumCall619Via622Chunk01From608From860From861.values ++
  MaximumCall619Via622Chunk02From608From860From861.values ++
  MaximumCall619Via622Chunk03From608From860From861.values ++
  MaximumCall619Via622Chunk04From608From860From861.values ++
  MaximumCall619Via622Chunk05From608From860From861.values.

Lemma values_eq :
  List.map MaximumCall619Via622ContextFrom608From860From861.depth MaximumCall619Via622ContextFrom608From860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 6
    MaximumCall619Via622ContextFrom608From860From861.depth MaximumCall619Via622ContextFrom608From860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall619Via622Chunk00From608From860From861.values_eq,
      MaximumCall619Via622Chunk01From608From860From861.values_eq,
      MaximumCall619Via622Chunk02From608From860From861.values_eq,
      MaximumCall619Via622Chunk03From608From860From861.values_eq,
      MaximumCall619Via622Chunk04From608From860From861.values_eq,
      MaximumCall619Via622Chunk05From608From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
