From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall612Via616From617ContextFrom608 MaximumCall612Via616From617Chunk00From608 MaximumCall612Via616From617Chunk01From608 MaximumCall612Via616From617Chunk02From608 MaximumCall612Via616From617Chunk03From608 MaximumCall612Via616From617Chunk04From608 MaximumCall612Via616From617Chunk05From608 MaximumCall612Via616From617Chunk06From608 MaximumCall612Via616From617Chunk07From608 MaximumCall612Via616From617Chunk08From608 MaximumCall612Via616From617Chunk09From608 MaximumCall612Via616From617Chunk10From608 MaximumCall612Via616From617Chunk11From608 MaximumCall612Via616From617Chunk12From608 MaximumCall612Via616From617Chunk13From608.

Definition values :=
  MaximumCall612Via616From617Chunk00From608.values ++
  MaximumCall612Via616From617Chunk01From608.values ++
  MaximumCall612Via616From617Chunk02From608.values ++
  MaximumCall612Via616From617Chunk03From608.values ++
  MaximumCall612Via616From617Chunk04From608.values ++
  MaximumCall612Via616From617Chunk05From608.values ++
  MaximumCall612Via616From617Chunk06From608.values ++
  MaximumCall612Via616From617Chunk07From608.values ++
  MaximumCall612Via616From617Chunk08From608.values ++
  MaximumCall612Via616From617Chunk09From608.values ++
  MaximumCall612Via616From617Chunk10From608.values ++
  MaximumCall612Via616From617Chunk11From608.values ++
  MaximumCall612Via616From617Chunk12From608.values ++
  MaximumCall612Via616From617Chunk13From608.values.

Lemma values_eq :
  List.map MaximumCall612Via616From617ContextFrom608.depth MaximumCall612Via616From617ContextFrom608.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 14
    MaximumCall612Via616From617ContextFrom608.depth MaximumCall612Via616From617ContextFrom608.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall612Via616From617Chunk00From608.values_eq,
      MaximumCall612Via616From617Chunk01From608.values_eq,
      MaximumCall612Via616From617Chunk02From608.values_eq,
      MaximumCall612Via616From617Chunk03From608.values_eq,
      MaximumCall612Via616From617Chunk04From608.values_eq,
      MaximumCall612Via616From617Chunk05From608.values_eq,
      MaximumCall612Via616From617Chunk06From608.values_eq,
      MaximumCall612Via616From617Chunk07From608.values_eq,
      MaximumCall612Via616From617Chunk08From608.values_eq,
      MaximumCall612Via616From617Chunk09From608.values_eq,
      MaximumCall612Via616From617Chunk10From608.values_eq,
      MaximumCall612Via616From617Chunk11From608.values_eq,
      MaximumCall612Via616From617Chunk12From608.values_eq,
      MaximumCall612Via616From617Chunk13From608.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
