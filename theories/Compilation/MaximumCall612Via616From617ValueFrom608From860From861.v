From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall612Via616From617ContextFrom608From860From861 MaximumCall612Via616From617Chunk00From608From860From861 MaximumCall612Via616From617Chunk01From608From860From861 MaximumCall612Via616From617Chunk02From608From860From861 MaximumCall612Via616From617Chunk03From608From860From861 MaximumCall612Via616From617Chunk04From608From860From861 MaximumCall612Via616From617Chunk05From608From860From861 MaximumCall612Via616From617Chunk06From608From860From861 MaximumCall612Via616From617Chunk07From608From860From861 MaximumCall612Via616From617Chunk08From608From860From861 MaximumCall612Via616From617Chunk09From608From860From861 MaximumCall612Via616From617Chunk10From608From860From861 MaximumCall612Via616From617Chunk11From608From860From861 MaximumCall612Via616From617Chunk12From608From860From861 MaximumCall612Via616From617Chunk13From608From860From861.

Definition values :=
  MaximumCall612Via616From617Chunk00From608From860From861.values ++
  MaximumCall612Via616From617Chunk01From608From860From861.values ++
  MaximumCall612Via616From617Chunk02From608From860From861.values ++
  MaximumCall612Via616From617Chunk03From608From860From861.values ++
  MaximumCall612Via616From617Chunk04From608From860From861.values ++
  MaximumCall612Via616From617Chunk05From608From860From861.values ++
  MaximumCall612Via616From617Chunk06From608From860From861.values ++
  MaximumCall612Via616From617Chunk07From608From860From861.values ++
  MaximumCall612Via616From617Chunk08From608From860From861.values ++
  MaximumCall612Via616From617Chunk09From608From860From861.values ++
  MaximumCall612Via616From617Chunk10From608From860From861.values ++
  MaximumCall612Via616From617Chunk11From608From860From861.values ++
  MaximumCall612Via616From617Chunk12From608From860From861.values ++
  MaximumCall612Via616From617Chunk13From608From860From861.values.

Lemma values_eq :
  List.map MaximumCall612Via616From617ContextFrom608From860From861.depth MaximumCall612Via616From617ContextFrom608From860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 14
    MaximumCall612Via616From617ContextFrom608From860From861.depth MaximumCall612Via616From617ContextFrom608From860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall612Via616From617Chunk00From608From860From861.values_eq,
      MaximumCall612Via616From617Chunk01From608From860From861.values_eq,
      MaximumCall612Via616From617Chunk02From608From860From861.values_eq,
      MaximumCall612Via616From617Chunk03From608From860From861.values_eq,
      MaximumCall612Via616From617Chunk04From608From860From861.values_eq,
      MaximumCall612Via616From617Chunk05From608From860From861.values_eq,
      MaximumCall612Via616From617Chunk06From608From860From861.values_eq,
      MaximumCall612Via616From617Chunk07From608From860From861.values_eq,
      MaximumCall612Via616From617Chunk08From608From860From861.values_eq,
      MaximumCall612Via616From617Chunk09From608From860From861.values_eq,
      MaximumCall612Via616From617Chunk10From608From860From861.values_eq,
      MaximumCall612Via616From617Chunk11From608From860From861.values_eq,
      MaximumCall612Via616From617Chunk12From608From860From861.values_eq,
      MaximumCall612Via616From617Chunk13From608From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
