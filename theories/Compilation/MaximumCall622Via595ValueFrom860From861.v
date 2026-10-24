From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall622Via595ContextFrom860From861 MaximumCall622Via595Chunk00From860From861 MaximumCall622Via595Chunk01From860From861 MaximumCall622Via595Chunk02From860From861 MaximumCall622Via595Chunk03From860From861 MaximumCall622Via595Chunk04From860From861 MaximumCall622Via595Chunk05From860From861 MaximumCall622Via595Chunk06From860From861 MaximumCall622Via595Chunk07From860From861 MaximumCall622Via595Chunk08From860From861 MaximumCall622Via595Chunk09From860From861 MaximumCall622Via595Chunk10From860From861 MaximumCall622Via595Chunk11From860From861 MaximumCall622Via595Chunk12From860From861 MaximumCall622Via595Chunk13From860From861 MaximumCall622Via595Chunk14From860From861 MaximumCall622Via595Chunk15From860From861 MaximumCall622Via595Chunk16From860From861 MaximumCall622Via595Chunk17From860From861.

Definition values :=
  MaximumCall622Via595Chunk00From860From861.values ++
  MaximumCall622Via595Chunk01From860From861.values ++
  MaximumCall622Via595Chunk02From860From861.values ++
  MaximumCall622Via595Chunk03From860From861.values ++
  MaximumCall622Via595Chunk04From860From861.values ++
  MaximumCall622Via595Chunk05From860From861.values ++
  MaximumCall622Via595Chunk06From860From861.values ++
  MaximumCall622Via595Chunk07From860From861.values ++
  MaximumCall622Via595Chunk08From860From861.values ++
  MaximumCall622Via595Chunk09From860From861.values ++
  MaximumCall622Via595Chunk10From860From861.values ++
  MaximumCall622Via595Chunk11From860From861.values ++
  MaximumCall622Via595Chunk12From860From861.values ++
  MaximumCall622Via595Chunk13From860From861.values ++
  MaximumCall622Via595Chunk14From860From861.values ++
  MaximumCall622Via595Chunk15From860From861.values ++
  MaximumCall622Via595Chunk16From860From861.values ++
  MaximumCall622Via595Chunk17From860From861.values.

Lemma values_eq :
  List.map MaximumCall622Via595ContextFrom860From861.depth MaximumCall622Via595ContextFrom860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 18
    MaximumCall622Via595ContextFrom860From861.depth MaximumCall622Via595ContextFrom860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall622Via595Chunk00From860From861.values_eq,
      MaximumCall622Via595Chunk01From860From861.values_eq,
      MaximumCall622Via595Chunk02From860From861.values_eq,
      MaximumCall622Via595Chunk03From860From861.values_eq,
      MaximumCall622Via595Chunk04From860From861.values_eq,
      MaximumCall622Via595Chunk05From860From861.values_eq,
      MaximumCall622Via595Chunk06From860From861.values_eq,
      MaximumCall622Via595Chunk07From860From861.values_eq,
      MaximumCall622Via595Chunk08From860From861.values_eq,
      MaximumCall622Via595Chunk09From860From861.values_eq,
      MaximumCall622Via595Chunk10From860From861.values_eq,
      MaximumCall622Via595Chunk11From860From861.values_eq,
      MaximumCall622Via595Chunk12From860From861.values_eq,
      MaximumCall622Via595Chunk13From860From861.values_eq,
      MaximumCall622Via595Chunk14From860From861.values_eq,
      MaximumCall622Via595Chunk15From860From861.values_eq,
      MaximumCall622Via595Chunk16From860From861.values_eq,
      MaximumCall622Via595Chunk17From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
