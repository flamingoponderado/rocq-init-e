From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall612Via616From618ContextFrom860From861 MaximumCall612Via616From618Chunk00From860From861 MaximumCall612Via616From618Chunk01From860From861 MaximumCall612Via616From618Chunk02From860From861 MaximumCall612Via616From618Chunk03From860From861 MaximumCall612Via616From618Chunk04From860From861 MaximumCall612Via616From618Chunk05From860From861 MaximumCall612Via616From618Chunk06From860From861 MaximumCall612Via616From618Chunk07From860From861 MaximumCall612Via616From618Chunk08From860From861 MaximumCall612Via616From618Chunk09From860From861 MaximumCall612Via616From618Chunk10From860From861 MaximumCall612Via616From618Chunk11From860From861 MaximumCall612Via616From618Chunk12From860From861 MaximumCall612Via616From618Chunk13From860From861.

Definition values :=
  MaximumCall612Via616From618Chunk00From860From861.values ++
  MaximumCall612Via616From618Chunk01From860From861.values ++
  MaximumCall612Via616From618Chunk02From860From861.values ++
  MaximumCall612Via616From618Chunk03From860From861.values ++
  MaximumCall612Via616From618Chunk04From860From861.values ++
  MaximumCall612Via616From618Chunk05From860From861.values ++
  MaximumCall612Via616From618Chunk06From860From861.values ++
  MaximumCall612Via616From618Chunk07From860From861.values ++
  MaximumCall612Via616From618Chunk08From860From861.values ++
  MaximumCall612Via616From618Chunk09From860From861.values ++
  MaximumCall612Via616From618Chunk10From860From861.values ++
  MaximumCall612Via616From618Chunk11From860From861.values ++
  MaximumCall612Via616From618Chunk12From860From861.values ++
  MaximumCall612Via616From618Chunk13From860From861.values.

Lemma values_eq :
  List.map MaximumCall612Via616From618ContextFrom860From861.depth MaximumCall612Via616From618ContextFrom860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 14
    MaximumCall612Via616From618ContextFrom860From861.depth MaximumCall612Via616From618ContextFrom860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall612Via616From618Chunk00From860From861.values_eq,
      MaximumCall612Via616From618Chunk01From860From861.values_eq,
      MaximumCall612Via616From618Chunk02From860From861.values_eq,
      MaximumCall612Via616From618Chunk03From860From861.values_eq,
      MaximumCall612Via616From618Chunk04From860From861.values_eq,
      MaximumCall612Via616From618Chunk05From860From861.values_eq,
      MaximumCall612Via616From618Chunk06From860From861.values_eq,
      MaximumCall612Via616From618Chunk07From860From861.values_eq,
      MaximumCall612Via616From618Chunk08From860From861.values_eq,
      MaximumCall612Via616From618Chunk09From860From861.values_eq,
      MaximumCall612Via616From618Chunk10From860From861.values_eq,
      MaximumCall612Via616From618Chunk11From860From861.values_eq,
      MaximumCall612Via616From618Chunk12From860From861.values_eq,
      MaximumCall612Via616From618Chunk13From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
