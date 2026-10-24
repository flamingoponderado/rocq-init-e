From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall598StructuredFrom606ContextFrom608From860 MaximumCall598StructuredFrom606Chunk00From608From860 MaximumCall598StructuredFrom606Chunk01From608From860 MaximumCall598StructuredFrom606Chunk02From608From860 MaximumCall598StructuredFrom606Chunk03From608From860 MaximumCall598StructuredFrom606Chunk04From608From860 MaximumCall598StructuredFrom606Chunk05From608From860 MaximumCall598StructuredFrom606Chunk06From608From860 MaximumCall598StructuredFrom606Chunk07From608From860 MaximumCall598StructuredFrom606Chunk08From608From860 MaximumCall598StructuredFrom606Chunk09From608From860 MaximumCall598StructuredFrom606Chunk10From608From860 MaximumCall598StructuredFrom606Chunk11From608From860.

Definition values :=
  MaximumCall598StructuredFrom606Chunk00From608From860.values ++
  MaximumCall598StructuredFrom606Chunk01From608From860.values ++
  MaximumCall598StructuredFrom606Chunk02From608From860.values ++
  MaximumCall598StructuredFrom606Chunk03From608From860.values ++
  MaximumCall598StructuredFrom606Chunk04From608From860.values ++
  MaximumCall598StructuredFrom606Chunk05From608From860.values ++
  MaximumCall598StructuredFrom606Chunk06From608From860.values ++
  MaximumCall598StructuredFrom606Chunk07From608From860.values ++
  MaximumCall598StructuredFrom606Chunk08From608From860.values ++
  MaximumCall598StructuredFrom606Chunk09From608From860.values ++
  MaximumCall598StructuredFrom606Chunk10From608From860.values ++
  MaximumCall598StructuredFrom606Chunk11From608From860.values.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom606ContextFrom608From860.depth MaximumCall598StructuredFrom606ContextFrom608From860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 12
    MaximumCall598StructuredFrom606ContextFrom608From860.depth MaximumCall598StructuredFrom606ContextFrom608From860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall598StructuredFrom606Chunk00From608From860.values_eq,
      MaximumCall598StructuredFrom606Chunk01From608From860.values_eq,
      MaximumCall598StructuredFrom606Chunk02From608From860.values_eq,
      MaximumCall598StructuredFrom606Chunk03From608From860.values_eq,
      MaximumCall598StructuredFrom606Chunk04From608From860.values_eq,
      MaximumCall598StructuredFrom606Chunk05From608From860.values_eq,
      MaximumCall598StructuredFrom606Chunk06From608From860.values_eq,
      MaximumCall598StructuredFrom606Chunk07From608From860.values_eq,
      MaximumCall598StructuredFrom606Chunk08From608From860.values_eq,
      MaximumCall598StructuredFrom606Chunk09From608From860.values_eq,
      MaximumCall598StructuredFrom606Chunk10From608From860.values_eq,
      MaximumCall598StructuredFrom606Chunk11From608From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
