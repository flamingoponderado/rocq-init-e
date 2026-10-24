From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall617Via595ContextFrom860From861 MaximumCall617Via595Chunk00From860From861 MaximumCall617Via595Chunk01From860From861 MaximumCall617Via595Chunk02From860From861 MaximumCall617Via595Chunk03From860From861 MaximumCall617Via595Chunk04From860From861 MaximumCall617Via595Chunk05From860From861 MaximumCall617Via595Chunk06From860From861 MaximumCall617Via595Chunk07From860From861 MaximumCall617Via595Chunk08From860From861.

Definition values :=
  MaximumCall617Via595Chunk00From860From861.values ++
  MaximumCall617Via595Chunk01From860From861.values ++
  MaximumCall617Via595Chunk02From860From861.values ++
  MaximumCall617Via595Chunk03From860From861.values ++
  MaximumCall617Via595Chunk04From860From861.values ++
  MaximumCall617Via595Chunk05From860From861.values ++
  MaximumCall617Via595Chunk06From860From861.values ++
  MaximumCall617Via595Chunk07From860From861.values ++
  MaximumCall617Via595Chunk08From860From861.values.

Lemma values_eq :
  List.map MaximumCall617Via595ContextFrom860From861.depth MaximumCall617Via595ContextFrom860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 9
    MaximumCall617Via595ContextFrom860From861.depth MaximumCall617Via595ContextFrom860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall617Via595Chunk00From860From861.values_eq,
      MaximumCall617Via595Chunk01From860From861.values_eq,
      MaximumCall617Via595Chunk02From860From861.values_eq,
      MaximumCall617Via595Chunk03From860From861.values_eq,
      MaximumCall617Via595Chunk04From860From861.values_eq,
      MaximumCall617Via595Chunk05From860From861.values_eq,
      MaximumCall617Via595Chunk06From860From861.values_eq,
      MaximumCall617Via595Chunk07From860From861.values_eq,
      MaximumCall617Via595Chunk08From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
