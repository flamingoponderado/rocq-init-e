From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall598StructuredFrom619From624ContextFrom608 MaximumCall598StructuredFrom619From624Chunk00From608 MaximumCall598StructuredFrom619From624Chunk01From608 MaximumCall598StructuredFrom619From624Chunk02From608 MaximumCall598StructuredFrom619From624Chunk03From608 MaximumCall598StructuredFrom619From624Chunk04From608 MaximumCall598StructuredFrom619From624Chunk05From608 MaximumCall598StructuredFrom619From624Chunk06From608 MaximumCall598StructuredFrom619From624Chunk07From608 MaximumCall598StructuredFrom619From624Chunk08From608 MaximumCall598StructuredFrom619From624Chunk09From608 MaximumCall598StructuredFrom619From624Chunk10From608 MaximumCall598StructuredFrom619From624Chunk11From608.

Definition values :=
  MaximumCall598StructuredFrom619From624Chunk00From608.values ++
  MaximumCall598StructuredFrom619From624Chunk01From608.values ++
  MaximumCall598StructuredFrom619From624Chunk02From608.values ++
  MaximumCall598StructuredFrom619From624Chunk03From608.values ++
  MaximumCall598StructuredFrom619From624Chunk04From608.values ++
  MaximumCall598StructuredFrom619From624Chunk05From608.values ++
  MaximumCall598StructuredFrom619From624Chunk06From608.values ++
  MaximumCall598StructuredFrom619From624Chunk07From608.values ++
  MaximumCall598StructuredFrom619From624Chunk08From608.values ++
  MaximumCall598StructuredFrom619From624Chunk09From608.values ++
  MaximumCall598StructuredFrom619From624Chunk10From608.values ++
  MaximumCall598StructuredFrom619From624Chunk11From608.values.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom619From624ContextFrom608.depth MaximumCall598StructuredFrom619From624ContextFrom608.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 12
    MaximumCall598StructuredFrom619From624ContextFrom608.depth MaximumCall598StructuredFrom619From624ContextFrom608.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall598StructuredFrom619From624Chunk00From608.values_eq,
      MaximumCall598StructuredFrom619From624Chunk01From608.values_eq,
      MaximumCall598StructuredFrom619From624Chunk02From608.values_eq,
      MaximumCall598StructuredFrom619From624Chunk03From608.values_eq,
      MaximumCall598StructuredFrom619From624Chunk04From608.values_eq,
      MaximumCall598StructuredFrom619From624Chunk05From608.values_eq,
      MaximumCall598StructuredFrom619From624Chunk06From608.values_eq,
      MaximumCall598StructuredFrom619From624Chunk07From608.values_eq,
      MaximumCall598StructuredFrom619From624Chunk08From608.values_eq,
      MaximumCall598StructuredFrom619From624Chunk09From608.values_eq,
      MaximumCall598StructuredFrom619From624Chunk10From608.values_eq,
      MaximumCall598StructuredFrom619From624Chunk11From608.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
