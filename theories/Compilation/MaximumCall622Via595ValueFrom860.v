From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall622Via595ContextFrom860 MaximumCall622Via595Chunk00From860 MaximumCall622Via595Chunk01From860 MaximumCall622Via595Chunk02From860 MaximumCall622Via595Chunk03From860 MaximumCall622Via595Chunk04From860 MaximumCall622Via595Chunk05From860 MaximumCall622Via595Chunk06From860 MaximumCall622Via595Chunk07From860 MaximumCall622Via595Chunk08From860 MaximumCall622Via595Chunk09From860 MaximumCall622Via595Chunk10From860 MaximumCall622Via595Chunk11From860 MaximumCall622Via595Chunk12From860 MaximumCall622Via595Chunk13From860 MaximumCall622Via595Chunk14From860 MaximumCall622Via595Chunk15From860 MaximumCall622Via595Chunk16From860 MaximumCall622Via595Chunk17From860.

Definition values :=
  MaximumCall622Via595Chunk00From860.values ++
  MaximumCall622Via595Chunk01From860.values ++
  MaximumCall622Via595Chunk02From860.values ++
  MaximumCall622Via595Chunk03From860.values ++
  MaximumCall622Via595Chunk04From860.values ++
  MaximumCall622Via595Chunk05From860.values ++
  MaximumCall622Via595Chunk06From860.values ++
  MaximumCall622Via595Chunk07From860.values ++
  MaximumCall622Via595Chunk08From860.values ++
  MaximumCall622Via595Chunk09From860.values ++
  MaximumCall622Via595Chunk10From860.values ++
  MaximumCall622Via595Chunk11From860.values ++
  MaximumCall622Via595Chunk12From860.values ++
  MaximumCall622Via595Chunk13From860.values ++
  MaximumCall622Via595Chunk14From860.values ++
  MaximumCall622Via595Chunk15From860.values ++
  MaximumCall622Via595Chunk16From860.values ++
  MaximumCall622Via595Chunk17From860.values.

Lemma values_eq :
  List.map MaximumCall622Via595ContextFrom860.depth MaximumCall622Via595ContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 18
    MaximumCall622Via595ContextFrom860.depth MaximumCall622Via595ContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall622Via595Chunk00From860.values_eq,
      MaximumCall622Via595Chunk01From860.values_eq,
      MaximumCall622Via595Chunk02From860.values_eq,
      MaximumCall622Via595Chunk03From860.values_eq,
      MaximumCall622Via595Chunk04From860.values_eq,
      MaximumCall622Via595Chunk05From860.values_eq,
      MaximumCall622Via595Chunk06From860.values_eq,
      MaximumCall622Via595Chunk07From860.values_eq,
      MaximumCall622Via595Chunk08From860.values_eq,
      MaximumCall622Via595Chunk09From860.values_eq,
      MaximumCall622Via595Chunk10From860.values_eq,
      MaximumCall622Via595Chunk11From860.values_eq,
      MaximumCall622Via595Chunk12From860.values_eq,
      MaximumCall622Via595Chunk13From860.values_eq,
      MaximumCall622Via595Chunk14From860.values_eq,
      MaximumCall622Via595Chunk15From860.values_eq,
      MaximumCall622Via595Chunk16From860.values_eq,
      MaximumCall622Via595Chunk17From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
