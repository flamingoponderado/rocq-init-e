From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall622Via595ContextFrom608 MaximumCall622Via595Chunk00From608 MaximumCall622Via595Chunk01From608 MaximumCall622Via595Chunk02From608 MaximumCall622Via595Chunk03From608 MaximumCall622Via595Chunk04From608 MaximumCall622Via595Chunk05From608 MaximumCall622Via595Chunk06From608 MaximumCall622Via595Chunk07From608 MaximumCall622Via595Chunk08From608 MaximumCall622Via595Chunk09From608 MaximumCall622Via595Chunk10From608 MaximumCall622Via595Chunk11From608 MaximumCall622Via595Chunk12From608 MaximumCall622Via595Chunk13From608 MaximumCall622Via595Chunk14From608 MaximumCall622Via595Chunk15From608 MaximumCall622Via595Chunk16From608 MaximumCall622Via595Chunk17From608.

Definition values :=
  MaximumCall622Via595Chunk00From608.values ++
  MaximumCall622Via595Chunk01From608.values ++
  MaximumCall622Via595Chunk02From608.values ++
  MaximumCall622Via595Chunk03From608.values ++
  MaximumCall622Via595Chunk04From608.values ++
  MaximumCall622Via595Chunk05From608.values ++
  MaximumCall622Via595Chunk06From608.values ++
  MaximumCall622Via595Chunk07From608.values ++
  MaximumCall622Via595Chunk08From608.values ++
  MaximumCall622Via595Chunk09From608.values ++
  MaximumCall622Via595Chunk10From608.values ++
  MaximumCall622Via595Chunk11From608.values ++
  MaximumCall622Via595Chunk12From608.values ++
  MaximumCall622Via595Chunk13From608.values ++
  MaximumCall622Via595Chunk14From608.values ++
  MaximumCall622Via595Chunk15From608.values ++
  MaximumCall622Via595Chunk16From608.values ++
  MaximumCall622Via595Chunk17From608.values.

Lemma values_eq :
  List.map MaximumCall622Via595ContextFrom608.depth MaximumCall622Via595ContextFrom608.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 18
    MaximumCall622Via595ContextFrom608.depth MaximumCall622Via595ContextFrom608.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall622Via595Chunk00From608.values_eq,
      MaximumCall622Via595Chunk01From608.values_eq,
      MaximumCall622Via595Chunk02From608.values_eq,
      MaximumCall622Via595Chunk03From608.values_eq,
      MaximumCall622Via595Chunk04From608.values_eq,
      MaximumCall622Via595Chunk05From608.values_eq,
      MaximumCall622Via595Chunk06From608.values_eq,
      MaximumCall622Via595Chunk07From608.values_eq,
      MaximumCall622Via595Chunk08From608.values_eq,
      MaximumCall622Via595Chunk09From608.values_eq,
      MaximumCall622Via595Chunk10From608.values_eq,
      MaximumCall622Via595Chunk11From608.values_eq,
      MaximumCall622Via595Chunk12From608.values_eq,
      MaximumCall622Via595Chunk13From608.values_eq,
      MaximumCall622Via595Chunk14From608.values_eq,
      MaximumCall622Via595Chunk15From608.values_eq,
      MaximumCall622Via595Chunk16From608.values_eq,
      MaximumCall622Via595Chunk17From608.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
