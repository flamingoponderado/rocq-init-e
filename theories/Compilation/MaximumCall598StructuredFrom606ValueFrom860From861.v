From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall598StructuredFrom606ContextFrom860From861 MaximumCall598StructuredFrom606Chunk00From860From861 MaximumCall598StructuredFrom606Chunk01From860From861 MaximumCall598StructuredFrom606Chunk02From860From861 MaximumCall598StructuredFrom606Chunk03From860From861 MaximumCall598StructuredFrom606Chunk04From860From861 MaximumCall598StructuredFrom606Chunk05From860From861 MaximumCall598StructuredFrom606Chunk06From860From861 MaximumCall598StructuredFrom606Chunk07From860From861 MaximumCall598StructuredFrom606Chunk08From860From861 MaximumCall598StructuredFrom606Chunk09From860From861 MaximumCall598StructuredFrom606Chunk10From860From861 MaximumCall598StructuredFrom606Chunk11From860From861.

Definition values :=
  MaximumCall598StructuredFrom606Chunk00From860From861.values ++
  MaximumCall598StructuredFrom606Chunk01From860From861.values ++
  MaximumCall598StructuredFrom606Chunk02From860From861.values ++
  MaximumCall598StructuredFrom606Chunk03From860From861.values ++
  MaximumCall598StructuredFrom606Chunk04From860From861.values ++
  MaximumCall598StructuredFrom606Chunk05From860From861.values ++
  MaximumCall598StructuredFrom606Chunk06From860From861.values ++
  MaximumCall598StructuredFrom606Chunk07From860From861.values ++
  MaximumCall598StructuredFrom606Chunk08From860From861.values ++
  MaximumCall598StructuredFrom606Chunk09From860From861.values ++
  MaximumCall598StructuredFrom606Chunk10From860From861.values ++
  MaximumCall598StructuredFrom606Chunk11From860From861.values.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom606ContextFrom860From861.depth MaximumCall598StructuredFrom606ContextFrom860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 12
    MaximumCall598StructuredFrom606ContextFrom860From861.depth MaximumCall598StructuredFrom606ContextFrom860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall598StructuredFrom606Chunk00From860From861.values_eq,
      MaximumCall598StructuredFrom606Chunk01From860From861.values_eq,
      MaximumCall598StructuredFrom606Chunk02From860From861.values_eq,
      MaximumCall598StructuredFrom606Chunk03From860From861.values_eq,
      MaximumCall598StructuredFrom606Chunk04From860From861.values_eq,
      MaximumCall598StructuredFrom606Chunk05From860From861.values_eq,
      MaximumCall598StructuredFrom606Chunk06From860From861.values_eq,
      MaximumCall598StructuredFrom606Chunk07From860From861.values_eq,
      MaximumCall598StructuredFrom606Chunk08From860From861.values_eq,
      MaximumCall598StructuredFrom606Chunk09From860From861.values_eq,
      MaximumCall598StructuredFrom606Chunk10From860From861.values_eq,
      MaximumCall598StructuredFrom606Chunk11From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
