From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall615Via618ContextFrom608From860From861 MaximumCall615Via618Chunk00From608From860From861 MaximumCall615Via618Chunk01From608From860From861 MaximumCall615Via618Chunk02From608From860From861 MaximumCall615Via618Chunk03From608From860From861 MaximumCall615Via618Chunk04From608From860From861 MaximumCall615Via618Chunk05From608From860From861 MaximumCall615Via618Chunk06From608From860From861.

Definition values :=
  MaximumCall615Via618Chunk00From608From860From861.values ++
  MaximumCall615Via618Chunk01From608From860From861.values ++
  MaximumCall615Via618Chunk02From608From860From861.values ++
  MaximumCall615Via618Chunk03From608From860From861.values ++
  MaximumCall615Via618Chunk04From608From860From861.values ++
  MaximumCall615Via618Chunk05From608From860From861.values ++
  MaximumCall615Via618Chunk06From608From860From861.values.

Lemma values_eq :
  List.map MaximumCall615Via618ContextFrom608From860From861.depth MaximumCall615Via618ContextFrom608From860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 7
    MaximumCall615Via618ContextFrom608From860From861.depth MaximumCall615Via618ContextFrom608From860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall615Via618Chunk00From608From860From861.values_eq,
      MaximumCall615Via618Chunk01From608From860From861.values_eq,
      MaximumCall615Via618Chunk02From608From860From861.values_eq,
      MaximumCall615Via618Chunk03From608From860From861.values_eq,
      MaximumCall615Via618Chunk04From608From860From861.values_eq,
      MaximumCall615Via618Chunk05From608From860From861.values_eq,
      MaximumCall615Via618Chunk06From608From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
