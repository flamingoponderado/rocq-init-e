From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall598StructuredFrom619From622ContextFrom608 MaximumCall598StructuredFrom619From622Chunk00From608 MaximumCall598StructuredFrom619From622Chunk01From608 MaximumCall598StructuredFrom619From622Chunk02From608 MaximumCall598StructuredFrom619From622Chunk03From608 MaximumCall598StructuredFrom619From622Chunk04From608 MaximumCall598StructuredFrom619From622Chunk05From608 MaximumCall598StructuredFrom619From622Chunk06From608 MaximumCall598StructuredFrom619From622Chunk07From608 MaximumCall598StructuredFrom619From622Chunk08From608 MaximumCall598StructuredFrom619From622Chunk09From608 MaximumCall598StructuredFrom619From622Chunk10From608 MaximumCall598StructuredFrom619From622Chunk11From608.

Definition values :=
  MaximumCall598StructuredFrom619From622Chunk00From608.values ++
  MaximumCall598StructuredFrom619From622Chunk01From608.values ++
  MaximumCall598StructuredFrom619From622Chunk02From608.values ++
  MaximumCall598StructuredFrom619From622Chunk03From608.values ++
  MaximumCall598StructuredFrom619From622Chunk04From608.values ++
  MaximumCall598StructuredFrom619From622Chunk05From608.values ++
  MaximumCall598StructuredFrom619From622Chunk06From608.values ++
  MaximumCall598StructuredFrom619From622Chunk07From608.values ++
  MaximumCall598StructuredFrom619From622Chunk08From608.values ++
  MaximumCall598StructuredFrom619From622Chunk09From608.values ++
  MaximumCall598StructuredFrom619From622Chunk10From608.values ++
  MaximumCall598StructuredFrom619From622Chunk11From608.values.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom619From622ContextFrom608.depth MaximumCall598StructuredFrom619From622ContextFrom608.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 12
    MaximumCall598StructuredFrom619From622ContextFrom608.depth MaximumCall598StructuredFrom619From622ContextFrom608.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall598StructuredFrom619From622Chunk00From608.values_eq,
      MaximumCall598StructuredFrom619From622Chunk01From608.values_eq,
      MaximumCall598StructuredFrom619From622Chunk02From608.values_eq,
      MaximumCall598StructuredFrom619From622Chunk03From608.values_eq,
      MaximumCall598StructuredFrom619From622Chunk04From608.values_eq,
      MaximumCall598StructuredFrom619From622Chunk05From608.values_eq,
      MaximumCall598StructuredFrom619From622Chunk06From608.values_eq,
      MaximumCall598StructuredFrom619From622Chunk07From608.values_eq,
      MaximumCall598StructuredFrom619From622Chunk08From608.values_eq,
      MaximumCall598StructuredFrom619From622Chunk09From608.values_eq,
      MaximumCall598StructuredFrom619From622Chunk10From608.values_eq,
      MaximumCall598StructuredFrom619From622Chunk11From608.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
