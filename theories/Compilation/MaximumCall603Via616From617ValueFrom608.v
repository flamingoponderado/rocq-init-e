From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall603Via616From617ContextFrom608 MaximumCall603Via616From617Chunk00From608 MaximumCall603Via616From617Chunk01From608 MaximumCall603Via616From617Chunk02From608 MaximumCall603Via616From617Chunk03From608 MaximumCall603Via616From617Chunk04From608 MaximumCall603Via616From617Chunk05From608 MaximumCall603Via616From617Chunk06From608 MaximumCall603Via616From617Chunk07From608 MaximumCall603Via616From617Chunk08From608.

Definition values :=
  MaximumCall603Via616From617Chunk00From608.values ++
  MaximumCall603Via616From617Chunk01From608.values ++
  MaximumCall603Via616From617Chunk02From608.values ++
  MaximumCall603Via616From617Chunk03From608.values ++
  MaximumCall603Via616From617Chunk04From608.values ++
  MaximumCall603Via616From617Chunk05From608.values ++
  MaximumCall603Via616From617Chunk06From608.values ++
  MaximumCall603Via616From617Chunk07From608.values ++
  MaximumCall603Via616From617Chunk08From608.values.

Lemma values_eq :
  List.map MaximumCall603Via616From617ContextFrom608.depth MaximumCall603Via616From617ContextFrom608.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 9
    MaximumCall603Via616From617ContextFrom608.depth MaximumCall603Via616From617ContextFrom608.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall603Via616From617Chunk00From608.values_eq,
      MaximumCall603Via616From617Chunk01From608.values_eq,
      MaximumCall603Via616From617Chunk02From608.values_eq,
      MaximumCall603Via616From617Chunk03From608.values_eq,
      MaximumCall603Via616From617Chunk04From608.values_eq,
      MaximumCall603Via616From617Chunk05From608.values_eq,
      MaximumCall603Via616From617Chunk06From608.values_eq,
      MaximumCall603Via616From617Chunk07From608.values_eq,
      MaximumCall603Via616From617Chunk08From608.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
