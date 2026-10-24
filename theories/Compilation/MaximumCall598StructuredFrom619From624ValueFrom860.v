From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall598StructuredFrom619From624ContextFrom860 MaximumCall598StructuredFrom619From624Chunk00From860 MaximumCall598StructuredFrom619From624Chunk01From860 MaximumCall598StructuredFrom619From624Chunk02From860 MaximumCall598StructuredFrom619From624Chunk03From860 MaximumCall598StructuredFrom619From624Chunk04From860 MaximumCall598StructuredFrom619From624Chunk05From860 MaximumCall598StructuredFrom619From624Chunk06From860 MaximumCall598StructuredFrom619From624Chunk07From860 MaximumCall598StructuredFrom619From624Chunk08From860 MaximumCall598StructuredFrom619From624Chunk09From860 MaximumCall598StructuredFrom619From624Chunk10From860 MaximumCall598StructuredFrom619From624Chunk11From860.

Definition values :=
  MaximumCall598StructuredFrom619From624Chunk00From860.values ++
  MaximumCall598StructuredFrom619From624Chunk01From860.values ++
  MaximumCall598StructuredFrom619From624Chunk02From860.values ++
  MaximumCall598StructuredFrom619From624Chunk03From860.values ++
  MaximumCall598StructuredFrom619From624Chunk04From860.values ++
  MaximumCall598StructuredFrom619From624Chunk05From860.values ++
  MaximumCall598StructuredFrom619From624Chunk06From860.values ++
  MaximumCall598StructuredFrom619From624Chunk07From860.values ++
  MaximumCall598StructuredFrom619From624Chunk08From860.values ++
  MaximumCall598StructuredFrom619From624Chunk09From860.values ++
  MaximumCall598StructuredFrom619From624Chunk10From860.values ++
  MaximumCall598StructuredFrom619From624Chunk11From860.values.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom619From624ContextFrom860.depth MaximumCall598StructuredFrom619From624ContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 12
    MaximumCall598StructuredFrom619From624ContextFrom860.depth MaximumCall598StructuredFrom619From624ContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall598StructuredFrom619From624Chunk00From860.values_eq,
      MaximumCall598StructuredFrom619From624Chunk01From860.values_eq,
      MaximumCall598StructuredFrom619From624Chunk02From860.values_eq,
      MaximumCall598StructuredFrom619From624Chunk03From860.values_eq,
      MaximumCall598StructuredFrom619From624Chunk04From860.values_eq,
      MaximumCall598StructuredFrom619From624Chunk05From860.values_eq,
      MaximumCall598StructuredFrom619From624Chunk06From860.values_eq,
      MaximumCall598StructuredFrom619From624Chunk07From860.values_eq,
      MaximumCall598StructuredFrom619From624Chunk08From860.values_eq,
      MaximumCall598StructuredFrom619From624Chunk09From860.values_eq,
      MaximumCall598StructuredFrom619From624Chunk10From860.values_eq,
      MaximumCall598StructuredFrom619From624Chunk11From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
