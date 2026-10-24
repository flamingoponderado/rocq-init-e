From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall616Via618ContextFrom608From860 MaximumCall616Via618Chunk00From608From860 MaximumCall616Via618Chunk01From608From860 MaximumCall616Via618Chunk02From608From860 MaximumCall616Via618Chunk03From608From860 MaximumCall616Via618Chunk04From608From860 MaximumCall616Via618Chunk05From608From860 MaximumCall616Via618Chunk06From608From860 MaximumCall616Via618Chunk07From608From860 MaximumCall616Via618Chunk08From608From860 MaximumCall616Via618Chunk09From608From860 MaximumCall616Via618Chunk10From608From860 MaximumCall616Via618Chunk11From608From860 MaximumCall616Via618Chunk12From608From860 MaximumCall616Via618Chunk13From608From860 MaximumCall616Via618Chunk14From608From860 MaximumCall616Via618Chunk15From608From860 MaximumCall616Via618Chunk16From608From860.

Definition values :=
  MaximumCall616Via618Chunk00From608From860.values ++
  MaximumCall616Via618Chunk01From608From860.values ++
  MaximumCall616Via618Chunk02From608From860.values ++
  MaximumCall616Via618Chunk03From608From860.values ++
  MaximumCall616Via618Chunk04From608From860.values ++
  MaximumCall616Via618Chunk05From608From860.values ++
  MaximumCall616Via618Chunk06From608From860.values ++
  MaximumCall616Via618Chunk07From608From860.values ++
  MaximumCall616Via618Chunk08From608From860.values ++
  MaximumCall616Via618Chunk09From608From860.values ++
  MaximumCall616Via618Chunk10From608From860.values ++
  MaximumCall616Via618Chunk11From608From860.values ++
  MaximumCall616Via618Chunk12From608From860.values ++
  MaximumCall616Via618Chunk13From608From860.values ++
  MaximumCall616Via618Chunk14From608From860.values ++
  MaximumCall616Via618Chunk15From608From860.values ++
  MaximumCall616Via618Chunk16From608From860.values.

Lemma values_eq :
  List.map MaximumCall616Via618ContextFrom608From860.depth MaximumCall616Via618ContextFrom608From860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 17
    MaximumCall616Via618ContextFrom608From860.depth MaximumCall616Via618ContextFrom608From860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall616Via618Chunk00From608From860.values_eq,
      MaximumCall616Via618Chunk01From608From860.values_eq,
      MaximumCall616Via618Chunk02From608From860.values_eq,
      MaximumCall616Via618Chunk03From608From860.values_eq,
      MaximumCall616Via618Chunk04From608From860.values_eq,
      MaximumCall616Via618Chunk05From608From860.values_eq,
      MaximumCall616Via618Chunk06From608From860.values_eq,
      MaximumCall616Via618Chunk07From608From860.values_eq,
      MaximumCall616Via618Chunk08From608From860.values_eq,
      MaximumCall616Via618Chunk09From608From860.values_eq,
      MaximumCall616Via618Chunk10From608From860.values_eq,
      MaximumCall616Via618Chunk11From608From860.values_eq,
      MaximumCall616Via618Chunk12From608From860.values_eq,
      MaximumCall616Via618Chunk13From608From860.values_eq,
      MaximumCall616Via618Chunk14From608From860.values_eq,
      MaximumCall616Via618Chunk15From608From860.values_eq,
      MaximumCall616Via618Chunk16From608From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
