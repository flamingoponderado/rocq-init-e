From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall617Via595ContextFrom860 MaximumCall617Via595Chunk00From860 MaximumCall617Via595Chunk01From860 MaximumCall617Via595Chunk02From860 MaximumCall617Via595Chunk03From860 MaximumCall617Via595Chunk04From860 MaximumCall617Via595Chunk05From860 MaximumCall617Via595Chunk06From860 MaximumCall617Via595Chunk07From860 MaximumCall617Via595Chunk08From860.

Definition values :=
  MaximumCall617Via595Chunk00From860.values ++
  MaximumCall617Via595Chunk01From860.values ++
  MaximumCall617Via595Chunk02From860.values ++
  MaximumCall617Via595Chunk03From860.values ++
  MaximumCall617Via595Chunk04From860.values ++
  MaximumCall617Via595Chunk05From860.values ++
  MaximumCall617Via595Chunk06From860.values ++
  MaximumCall617Via595Chunk07From860.values ++
  MaximumCall617Via595Chunk08From860.values.

Lemma values_eq :
  List.map MaximumCall617Via595ContextFrom860.depth MaximumCall617Via595ContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 9
    MaximumCall617Via595ContextFrom860.depth MaximumCall617Via595ContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall617Via595Chunk00From860.values_eq,
      MaximumCall617Via595Chunk01From860.values_eq,
      MaximumCall617Via595Chunk02From860.values_eq,
      MaximumCall617Via595Chunk03From860.values_eq,
      MaximumCall617Via595Chunk04From860.values_eq,
      MaximumCall617Via595Chunk05From860.values_eq,
      MaximumCall617Via595Chunk06From860.values_eq,
      MaximumCall617Via595Chunk07From860.values_eq,
      MaximumCall617Via595Chunk08From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
