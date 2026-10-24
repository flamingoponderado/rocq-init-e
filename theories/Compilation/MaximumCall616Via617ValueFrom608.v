From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall616Via617ContextFrom608 MaximumCall616Via617Chunk00From608 MaximumCall616Via617Chunk01From608 MaximumCall616Via617Chunk02From608 MaximumCall616Via617Chunk03From608 MaximumCall616Via617Chunk04From608 MaximumCall616Via617Chunk05From608 MaximumCall616Via617Chunk06From608 MaximumCall616Via617Chunk07From608 MaximumCall616Via617Chunk08From608 MaximumCall616Via617Chunk09From608 MaximumCall616Via617Chunk10From608 MaximumCall616Via617Chunk11From608 MaximumCall616Via617Chunk12From608 MaximumCall616Via617Chunk13From608 MaximumCall616Via617Chunk14From608 MaximumCall616Via617Chunk15From608 MaximumCall616Via617Chunk16From608.

Definition values :=
  MaximumCall616Via617Chunk00From608.values ++
  MaximumCall616Via617Chunk01From608.values ++
  MaximumCall616Via617Chunk02From608.values ++
  MaximumCall616Via617Chunk03From608.values ++
  MaximumCall616Via617Chunk04From608.values ++
  MaximumCall616Via617Chunk05From608.values ++
  MaximumCall616Via617Chunk06From608.values ++
  MaximumCall616Via617Chunk07From608.values ++
  MaximumCall616Via617Chunk08From608.values ++
  MaximumCall616Via617Chunk09From608.values ++
  MaximumCall616Via617Chunk10From608.values ++
  MaximumCall616Via617Chunk11From608.values ++
  MaximumCall616Via617Chunk12From608.values ++
  MaximumCall616Via617Chunk13From608.values ++
  MaximumCall616Via617Chunk14From608.values ++
  MaximumCall616Via617Chunk15From608.values ++
  MaximumCall616Via617Chunk16From608.values.

Lemma values_eq :
  List.map MaximumCall616Via617ContextFrom608.depth MaximumCall616Via617ContextFrom608.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 17
    MaximumCall616Via617ContextFrom608.depth MaximumCall616Via617ContextFrom608.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall616Via617Chunk00From608.values_eq,
      MaximumCall616Via617Chunk01From608.values_eq,
      MaximumCall616Via617Chunk02From608.values_eq,
      MaximumCall616Via617Chunk03From608.values_eq,
      MaximumCall616Via617Chunk04From608.values_eq,
      MaximumCall616Via617Chunk05From608.values_eq,
      MaximumCall616Via617Chunk06From608.values_eq,
      MaximumCall616Via617Chunk07From608.values_eq,
      MaximumCall616Via617Chunk08From608.values_eq,
      MaximumCall616Via617Chunk09From608.values_eq,
      MaximumCall616Via617Chunk10From608.values_eq,
      MaximumCall616Via617Chunk11From608.values_eq,
      MaximumCall616Via617Chunk12From608.values_eq,
      MaximumCall616Via617Chunk13From608.values_eq,
      MaximumCall616Via617Chunk14From608.values_eq,
      MaximumCall616Via617Chunk15From608.values_eq,
      MaximumCall616Via617Chunk16From608.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
