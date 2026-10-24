From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall616Via618ContextFrom860 MaximumCall616Via618Chunk00From860 MaximumCall616Via618Chunk01From860 MaximumCall616Via618Chunk02From860 MaximumCall616Via618Chunk03From860 MaximumCall616Via618Chunk04From860 MaximumCall616Via618Chunk05From860 MaximumCall616Via618Chunk06From860 MaximumCall616Via618Chunk07From860 MaximumCall616Via618Chunk08From860 MaximumCall616Via618Chunk09From860 MaximumCall616Via618Chunk10From860 MaximumCall616Via618Chunk11From860 MaximumCall616Via618Chunk12From860 MaximumCall616Via618Chunk13From860 MaximumCall616Via618Chunk14From860 MaximumCall616Via618Chunk15From860 MaximumCall616Via618Chunk16From860.

Definition values :=
  MaximumCall616Via618Chunk00From860.values ++
  MaximumCall616Via618Chunk01From860.values ++
  MaximumCall616Via618Chunk02From860.values ++
  MaximumCall616Via618Chunk03From860.values ++
  MaximumCall616Via618Chunk04From860.values ++
  MaximumCall616Via618Chunk05From860.values ++
  MaximumCall616Via618Chunk06From860.values ++
  MaximumCall616Via618Chunk07From860.values ++
  MaximumCall616Via618Chunk08From860.values ++
  MaximumCall616Via618Chunk09From860.values ++
  MaximumCall616Via618Chunk10From860.values ++
  MaximumCall616Via618Chunk11From860.values ++
  MaximumCall616Via618Chunk12From860.values ++
  MaximumCall616Via618Chunk13From860.values ++
  MaximumCall616Via618Chunk14From860.values ++
  MaximumCall616Via618Chunk15From860.values ++
  MaximumCall616Via618Chunk16From860.values.

Lemma values_eq :
  List.map MaximumCall616Via618ContextFrom860.depth MaximumCall616Via618ContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 17
    MaximumCall616Via618ContextFrom860.depth MaximumCall616Via618ContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall616Via618Chunk00From860.values_eq,
      MaximumCall616Via618Chunk01From860.values_eq,
      MaximumCall616Via618Chunk02From860.values_eq,
      MaximumCall616Via618Chunk03From860.values_eq,
      MaximumCall616Via618Chunk04From860.values_eq,
      MaximumCall616Via618Chunk05From860.values_eq,
      MaximumCall616Via618Chunk06From860.values_eq,
      MaximumCall616Via618Chunk07From860.values_eq,
      MaximumCall616Via618Chunk08From860.values_eq,
      MaximumCall616Via618Chunk09From860.values_eq,
      MaximumCall616Via618Chunk10From860.values_eq,
      MaximumCall616Via618Chunk11From860.values_eq,
      MaximumCall616Via618Chunk12From860.values_eq,
      MaximumCall616Via618Chunk13From860.values_eq,
      MaximumCall616Via618Chunk14From860.values_eq,
      MaximumCall616Via618Chunk15From860.values_eq,
      MaximumCall616Via618Chunk16From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
