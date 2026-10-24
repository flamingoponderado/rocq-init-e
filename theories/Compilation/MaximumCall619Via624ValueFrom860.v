From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall619Via624ContextFrom860 MaximumCall619Via624Chunk00From860 MaximumCall619Via624Chunk01From860 MaximumCall619Via624Chunk02From860 MaximumCall619Via624Chunk03From860 MaximumCall619Via624Chunk04From860 MaximumCall619Via624Chunk05From860.

Definition values :=
  MaximumCall619Via624Chunk00From860.values ++
  MaximumCall619Via624Chunk01From860.values ++
  MaximumCall619Via624Chunk02From860.values ++
  MaximumCall619Via624Chunk03From860.values ++
  MaximumCall619Via624Chunk04From860.values ++
  MaximumCall619Via624Chunk05From860.values.

Lemma values_eq :
  List.map MaximumCall619Via624ContextFrom860.depth MaximumCall619Via624ContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 6
    MaximumCall619Via624ContextFrom860.depth MaximumCall619Via624ContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall619Via624Chunk00From860.values_eq,
      MaximumCall619Via624Chunk01From860.values_eq,
      MaximumCall619Via624Chunk02From860.values_eq,
      MaximumCall619Via624Chunk03From860.values_eq,
      MaximumCall619Via624Chunk04From860.values_eq,
      MaximumCall619Via624Chunk05From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
