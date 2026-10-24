From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall598StructuredFrom616From618ContextFrom608 MaximumCall598StructuredFrom616From618Chunk00From608 MaximumCall598StructuredFrom616From618Chunk01From608 MaximumCall598StructuredFrom616From618Chunk02From608 MaximumCall598StructuredFrom616From618Chunk03From608 MaximumCall598StructuredFrom616From618Chunk04From608 MaximumCall598StructuredFrom616From618Chunk05From608 MaximumCall598StructuredFrom616From618Chunk06From608 MaximumCall598StructuredFrom616From618Chunk07From608 MaximumCall598StructuredFrom616From618Chunk08From608 MaximumCall598StructuredFrom616From618Chunk09From608 MaximumCall598StructuredFrom616From618Chunk10From608 MaximumCall598StructuredFrom616From618Chunk11From608.

Definition values :=
  MaximumCall598StructuredFrom616From618Chunk00From608.values ++
  MaximumCall598StructuredFrom616From618Chunk01From608.values ++
  MaximumCall598StructuredFrom616From618Chunk02From608.values ++
  MaximumCall598StructuredFrom616From618Chunk03From608.values ++
  MaximumCall598StructuredFrom616From618Chunk04From608.values ++
  MaximumCall598StructuredFrom616From618Chunk05From608.values ++
  MaximumCall598StructuredFrom616From618Chunk06From608.values ++
  MaximumCall598StructuredFrom616From618Chunk07From608.values ++
  MaximumCall598StructuredFrom616From618Chunk08From608.values ++
  MaximumCall598StructuredFrom616From618Chunk09From608.values ++
  MaximumCall598StructuredFrom616From618Chunk10From608.values ++
  MaximumCall598StructuredFrom616From618Chunk11From608.values.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom616From618ContextFrom608.depth MaximumCall598StructuredFrom616From618ContextFrom608.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 12
    MaximumCall598StructuredFrom616From618ContextFrom608.depth MaximumCall598StructuredFrom616From618ContextFrom608.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall598StructuredFrom616From618Chunk00From608.values_eq,
      MaximumCall598StructuredFrom616From618Chunk01From608.values_eq,
      MaximumCall598StructuredFrom616From618Chunk02From608.values_eq,
      MaximumCall598StructuredFrom616From618Chunk03From608.values_eq,
      MaximumCall598StructuredFrom616From618Chunk04From608.values_eq,
      MaximumCall598StructuredFrom616From618Chunk05From608.values_eq,
      MaximumCall598StructuredFrom616From618Chunk06From608.values_eq,
      MaximumCall598StructuredFrom616From618Chunk07From608.values_eq,
      MaximumCall598StructuredFrom616From618Chunk08From608.values_eq,
      MaximumCall598StructuredFrom616From618Chunk09From608.values_eq,
      MaximumCall598StructuredFrom616From618Chunk10From608.values_eq,
      MaximumCall598StructuredFrom616From618Chunk11From608.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
