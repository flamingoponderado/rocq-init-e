From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall616Via618ContextFrom608 MaximumCall616Via618Chunk00From608 MaximumCall616Via618Chunk01From608 MaximumCall616Via618Chunk02From608 MaximumCall616Via618Chunk03From608 MaximumCall616Via618Chunk04From608 MaximumCall616Via618Chunk05From608 MaximumCall616Via618Chunk06From608 MaximumCall616Via618Chunk07From608 MaximumCall616Via618Chunk08From608 MaximumCall616Via618Chunk09From608 MaximumCall616Via618Chunk10From608 MaximumCall616Via618Chunk11From608 MaximumCall616Via618Chunk12From608 MaximumCall616Via618Chunk13From608 MaximumCall616Via618Chunk14From608 MaximumCall616Via618Chunk15From608 MaximumCall616Via618Chunk16From608.

Definition values :=
  MaximumCall616Via618Chunk00From608.values ++
  MaximumCall616Via618Chunk01From608.values ++
  MaximumCall616Via618Chunk02From608.values ++
  MaximumCall616Via618Chunk03From608.values ++
  MaximumCall616Via618Chunk04From608.values ++
  MaximumCall616Via618Chunk05From608.values ++
  MaximumCall616Via618Chunk06From608.values ++
  MaximumCall616Via618Chunk07From608.values ++
  MaximumCall616Via618Chunk08From608.values ++
  MaximumCall616Via618Chunk09From608.values ++
  MaximumCall616Via618Chunk10From608.values ++
  MaximumCall616Via618Chunk11From608.values ++
  MaximumCall616Via618Chunk12From608.values ++
  MaximumCall616Via618Chunk13From608.values ++
  MaximumCall616Via618Chunk14From608.values ++
  MaximumCall616Via618Chunk15From608.values ++
  MaximumCall616Via618Chunk16From608.values.

Lemma values_eq :
  List.map MaximumCall616Via618ContextFrom608.depth MaximumCall616Via618ContextFrom608.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 17
    MaximumCall616Via618ContextFrom608.depth MaximumCall616Via618ContextFrom608.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall616Via618Chunk00From608.values_eq,
      MaximumCall616Via618Chunk01From608.values_eq,
      MaximumCall616Via618Chunk02From608.values_eq,
      MaximumCall616Via618Chunk03From608.values_eq,
      MaximumCall616Via618Chunk04From608.values_eq,
      MaximumCall616Via618Chunk05From608.values_eq,
      MaximumCall616Via618Chunk06From608.values_eq,
      MaximumCall616Via618Chunk07From608.values_eq,
      MaximumCall616Via618Chunk08From608.values_eq,
      MaximumCall616Via618Chunk09From608.values_eq,
      MaximumCall616Via618Chunk10From608.values_eq,
      MaximumCall616Via618Chunk11From608.values_eq,
      MaximumCall616Via618Chunk12From608.values_eq,
      MaximumCall616Via618Chunk13From608.values_eq,
      MaximumCall616Via618Chunk14From608.values_eq,
      MaximumCall616Via618Chunk15From608.values_eq,
      MaximumCall616Via618Chunk16From608.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
