From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall623Via595ContextFrom608From860 MaximumCall623Via595Chunk00From608From860 MaximumCall623Via595Chunk01From608From860 MaximumCall623Via595Chunk02From608From860 MaximumCall623Via595Chunk03From608From860 MaximumCall623Via595Chunk04From608From860 MaximumCall623Via595Chunk05From608From860 MaximumCall623Via595Chunk06From608From860 MaximumCall623Via595Chunk07From608From860 MaximumCall623Via595Chunk08From608From860 MaximumCall623Via595Chunk09From608From860 MaximumCall623Via595Chunk10From608From860 MaximumCall623Via595Chunk11From608From860 MaximumCall623Via595Chunk12From608From860 MaximumCall623Via595Chunk13From608From860 MaximumCall623Via595Chunk14From608From860 MaximumCall623Via595Chunk15From608From860 MaximumCall623Via595Chunk16From608From860 MaximumCall623Via595Chunk17From608From860.

Definition values :=
  MaximumCall623Via595Chunk00From608From860.values ++
  MaximumCall623Via595Chunk01From608From860.values ++
  MaximumCall623Via595Chunk02From608From860.values ++
  MaximumCall623Via595Chunk03From608From860.values ++
  MaximumCall623Via595Chunk04From608From860.values ++
  MaximumCall623Via595Chunk05From608From860.values ++
  MaximumCall623Via595Chunk06From608From860.values ++
  MaximumCall623Via595Chunk07From608From860.values ++
  MaximumCall623Via595Chunk08From608From860.values ++
  MaximumCall623Via595Chunk09From608From860.values ++
  MaximumCall623Via595Chunk10From608From860.values ++
  MaximumCall623Via595Chunk11From608From860.values ++
  MaximumCall623Via595Chunk12From608From860.values ++
  MaximumCall623Via595Chunk13From608From860.values ++
  MaximumCall623Via595Chunk14From608From860.values ++
  MaximumCall623Via595Chunk15From608From860.values ++
  MaximumCall623Via595Chunk16From608From860.values ++
  MaximumCall623Via595Chunk17From608From860.values.

Lemma values_eq :
  List.map MaximumCall623Via595ContextFrom608From860.depth MaximumCall623Via595ContextFrom608From860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 18
    MaximumCall623Via595ContextFrom608From860.depth MaximumCall623Via595ContextFrom608From860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall623Via595Chunk00From608From860.values_eq,
      MaximumCall623Via595Chunk01From608From860.values_eq,
      MaximumCall623Via595Chunk02From608From860.values_eq,
      MaximumCall623Via595Chunk03From608From860.values_eq,
      MaximumCall623Via595Chunk04From608From860.values_eq,
      MaximumCall623Via595Chunk05From608From860.values_eq,
      MaximumCall623Via595Chunk06From608From860.values_eq,
      MaximumCall623Via595Chunk07From608From860.values_eq,
      MaximumCall623Via595Chunk08From608From860.values_eq,
      MaximumCall623Via595Chunk09From608From860.values_eq,
      MaximumCall623Via595Chunk10From608From860.values_eq,
      MaximumCall623Via595Chunk11From608From860.values_eq,
      MaximumCall623Via595Chunk12From608From860.values_eq,
      MaximumCall623Via595Chunk13From608From860.values_eq,
      MaximumCall623Via595Chunk14From608From860.values_eq,
      MaximumCall623Via595Chunk15From608From860.values_eq,
      MaximumCall623Via595Chunk16From608From860.values_eq,
      MaximumCall623Via595Chunk17From608From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
