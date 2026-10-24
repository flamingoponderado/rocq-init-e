From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall598StructuredFrom616From618ContextFrom860 MaximumCall598StructuredFrom616From618Chunk00From860 MaximumCall598StructuredFrom616From618Chunk01From860 MaximumCall598StructuredFrom616From618Chunk02From860 MaximumCall598StructuredFrom616From618Chunk03From860 MaximumCall598StructuredFrom616From618Chunk04From860 MaximumCall598StructuredFrom616From618Chunk05From860 MaximumCall598StructuredFrom616From618Chunk06From860 MaximumCall598StructuredFrom616From618Chunk07From860 MaximumCall598StructuredFrom616From618Chunk08From860 MaximumCall598StructuredFrom616From618Chunk09From860 MaximumCall598StructuredFrom616From618Chunk10From860 MaximumCall598StructuredFrom616From618Chunk11From860.

Definition values :=
  MaximumCall598StructuredFrom616From618Chunk00From860.values ++
  MaximumCall598StructuredFrom616From618Chunk01From860.values ++
  MaximumCall598StructuredFrom616From618Chunk02From860.values ++
  MaximumCall598StructuredFrom616From618Chunk03From860.values ++
  MaximumCall598StructuredFrom616From618Chunk04From860.values ++
  MaximumCall598StructuredFrom616From618Chunk05From860.values ++
  MaximumCall598StructuredFrom616From618Chunk06From860.values ++
  MaximumCall598StructuredFrom616From618Chunk07From860.values ++
  MaximumCall598StructuredFrom616From618Chunk08From860.values ++
  MaximumCall598StructuredFrom616From618Chunk09From860.values ++
  MaximumCall598StructuredFrom616From618Chunk10From860.values ++
  MaximumCall598StructuredFrom616From618Chunk11From860.values.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom616From618ContextFrom860.depth MaximumCall598StructuredFrom616From618ContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 12
    MaximumCall598StructuredFrom616From618ContextFrom860.depth MaximumCall598StructuredFrom616From618ContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall598StructuredFrom616From618Chunk00From860.values_eq,
      MaximumCall598StructuredFrom616From618Chunk01From860.values_eq,
      MaximumCall598StructuredFrom616From618Chunk02From860.values_eq,
      MaximumCall598StructuredFrom616From618Chunk03From860.values_eq,
      MaximumCall598StructuredFrom616From618Chunk04From860.values_eq,
      MaximumCall598StructuredFrom616From618Chunk05From860.values_eq,
      MaximumCall598StructuredFrom616From618Chunk06From860.values_eq,
      MaximumCall598StructuredFrom616From618Chunk07From860.values_eq,
      MaximumCall598StructuredFrom616From618Chunk08From860.values_eq,
      MaximumCall598StructuredFrom616From618Chunk09From860.values_eq,
      MaximumCall598StructuredFrom616From618Chunk10From860.values_eq,
      MaximumCall598StructuredFrom616From618Chunk11From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
