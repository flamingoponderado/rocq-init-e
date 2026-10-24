From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall624Via595ContextFrom608From860 MaximumCall624Via595Chunk00From608From860 MaximumCall624Via595Chunk01From608From860 MaximumCall624Via595Chunk02From608From860 MaximumCall624Via595Chunk03From608From860 MaximumCall624Via595Chunk04From608From860 MaximumCall624Via595Chunk05From608From860 MaximumCall624Via595Chunk06From608From860 MaximumCall624Via595Chunk07From608From860 MaximumCall624Via595Chunk08From608From860 MaximumCall624Via595Chunk09From608From860 MaximumCall624Via595Chunk10From608From860 MaximumCall624Via595Chunk11From608From860 MaximumCall624Via595Chunk12From608From860 MaximumCall624Via595Chunk13From608From860 MaximumCall624Via595Chunk14From608From860 MaximumCall624Via595Chunk15From608From860 MaximumCall624Via595Chunk16From608From860.

Definition values :=
  MaximumCall624Via595Chunk00From608From860.values ++
  MaximumCall624Via595Chunk01From608From860.values ++
  MaximumCall624Via595Chunk02From608From860.values ++
  MaximumCall624Via595Chunk03From608From860.values ++
  MaximumCall624Via595Chunk04From608From860.values ++
  MaximumCall624Via595Chunk05From608From860.values ++
  MaximumCall624Via595Chunk06From608From860.values ++
  MaximumCall624Via595Chunk07From608From860.values ++
  MaximumCall624Via595Chunk08From608From860.values ++
  MaximumCall624Via595Chunk09From608From860.values ++
  MaximumCall624Via595Chunk10From608From860.values ++
  MaximumCall624Via595Chunk11From608From860.values ++
  MaximumCall624Via595Chunk12From608From860.values ++
  MaximumCall624Via595Chunk13From608From860.values ++
  MaximumCall624Via595Chunk14From608From860.values ++
  MaximumCall624Via595Chunk15From608From860.values ++
  MaximumCall624Via595Chunk16From608From860.values.

Lemma values_eq :
  List.map MaximumCall624Via595ContextFrom608From860.depth MaximumCall624Via595ContextFrom608From860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 17
    MaximumCall624Via595ContextFrom608From860.depth MaximumCall624Via595ContextFrom608From860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall624Via595Chunk00From608From860.values_eq,
      MaximumCall624Via595Chunk01From608From860.values_eq,
      MaximumCall624Via595Chunk02From608From860.values_eq,
      MaximumCall624Via595Chunk03From608From860.values_eq,
      MaximumCall624Via595Chunk04From608From860.values_eq,
      MaximumCall624Via595Chunk05From608From860.values_eq,
      MaximumCall624Via595Chunk06From608From860.values_eq,
      MaximumCall624Via595Chunk07From608From860.values_eq,
      MaximumCall624Via595Chunk08From608From860.values_eq,
      MaximumCall624Via595Chunk09From608From860.values_eq,
      MaximumCall624Via595Chunk10From608From860.values_eq,
      MaximumCall624Via595Chunk11From608From860.values_eq,
      MaximumCall624Via595Chunk12From608From860.values_eq,
      MaximumCall624Via595Chunk13From608From860.values_eq,
      MaximumCall624Via595Chunk14From608From860.values_eq,
      MaximumCall624Via595Chunk15From608From860.values_eq,
      MaximumCall624Via595Chunk16From608From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
