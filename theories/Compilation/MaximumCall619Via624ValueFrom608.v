From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall619Via624ContextFrom608 MaximumCall619Via624Chunk00From608 MaximumCall619Via624Chunk01From608 MaximumCall619Via624Chunk02From608 MaximumCall619Via624Chunk03From608 MaximumCall619Via624Chunk04From608 MaximumCall619Via624Chunk05From608.

Definition values :=
  MaximumCall619Via624Chunk00From608.values ++
  MaximumCall619Via624Chunk01From608.values ++
  MaximumCall619Via624Chunk02From608.values ++
  MaximumCall619Via624Chunk03From608.values ++
  MaximumCall619Via624Chunk04From608.values ++
  MaximumCall619Via624Chunk05From608.values.

Lemma values_eq :
  List.map MaximumCall619Via624ContextFrom608.depth MaximumCall619Via624ContextFrom608.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 6
    MaximumCall619Via624ContextFrom608.depth MaximumCall619Via624ContextFrom608.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall619Via624Chunk00From608.values_eq,
      MaximumCall619Via624Chunk01From608.values_eq,
      MaximumCall619Via624Chunk02From608.values_eq,
      MaximumCall619Via624Chunk03From608.values_eq,
      MaximumCall619Via624Chunk04From608.values_eq,
      MaximumCall619Via624Chunk05From608.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
