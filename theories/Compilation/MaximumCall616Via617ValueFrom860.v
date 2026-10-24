From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall616Via617ContextFrom860 MaximumCall616Via617Chunk00From860 MaximumCall616Via617Chunk01From860 MaximumCall616Via617Chunk02From860 MaximumCall616Via617Chunk03From860 MaximumCall616Via617Chunk04From860 MaximumCall616Via617Chunk05From860 MaximumCall616Via617Chunk06From860 MaximumCall616Via617Chunk07From860 MaximumCall616Via617Chunk08From860 MaximumCall616Via617Chunk09From860 MaximumCall616Via617Chunk10From860 MaximumCall616Via617Chunk11From860 MaximumCall616Via617Chunk12From860 MaximumCall616Via617Chunk13From860 MaximumCall616Via617Chunk14From860 MaximumCall616Via617Chunk15From860 MaximumCall616Via617Chunk16From860.

Definition values :=
  MaximumCall616Via617Chunk00From860.values ++
  MaximumCall616Via617Chunk01From860.values ++
  MaximumCall616Via617Chunk02From860.values ++
  MaximumCall616Via617Chunk03From860.values ++
  MaximumCall616Via617Chunk04From860.values ++
  MaximumCall616Via617Chunk05From860.values ++
  MaximumCall616Via617Chunk06From860.values ++
  MaximumCall616Via617Chunk07From860.values ++
  MaximumCall616Via617Chunk08From860.values ++
  MaximumCall616Via617Chunk09From860.values ++
  MaximumCall616Via617Chunk10From860.values ++
  MaximumCall616Via617Chunk11From860.values ++
  MaximumCall616Via617Chunk12From860.values ++
  MaximumCall616Via617Chunk13From860.values ++
  MaximumCall616Via617Chunk14From860.values ++
  MaximumCall616Via617Chunk15From860.values ++
  MaximumCall616Via617Chunk16From860.values.

Lemma values_eq :
  List.map MaximumCall616Via617ContextFrom860.depth MaximumCall616Via617ContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 17
    MaximumCall616Via617ContextFrom860.depth MaximumCall616Via617ContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall616Via617Chunk00From860.values_eq,
      MaximumCall616Via617Chunk01From860.values_eq,
      MaximumCall616Via617Chunk02From860.values_eq,
      MaximumCall616Via617Chunk03From860.values_eq,
      MaximumCall616Via617Chunk04From860.values_eq,
      MaximumCall616Via617Chunk05From860.values_eq,
      MaximumCall616Via617Chunk06From860.values_eq,
      MaximumCall616Via617Chunk07From860.values_eq,
      MaximumCall616Via617Chunk08From860.values_eq,
      MaximumCall616Via617Chunk09From860.values_eq,
      MaximumCall616Via617Chunk10From860.values_eq,
      MaximumCall616Via617Chunk11From860.values_eq,
      MaximumCall616Via617Chunk12From860.values_eq,
      MaximumCall616Via617Chunk13From860.values_eq,
      MaximumCall616Via617Chunk14From860.values_eq,
      MaximumCall616Via617Chunk15From860.values_eq,
      MaximumCall616Via617Chunk16From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
