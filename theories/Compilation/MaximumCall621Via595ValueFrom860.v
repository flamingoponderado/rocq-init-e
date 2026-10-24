From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall621Via595ContextFrom860 MaximumCall621Via595Chunk00From860 MaximumCall621Via595Chunk01From860 MaximumCall621Via595Chunk02From860 MaximumCall621Via595Chunk03From860 MaximumCall621Via595Chunk04From860 MaximumCall621Via595Chunk05From860 MaximumCall621Via595Chunk06From860 MaximumCall621Via595Chunk07From860 MaximumCall621Via595Chunk08From860 MaximumCall621Via595Chunk09From860 MaximumCall621Via595Chunk10From860 MaximumCall621Via595Chunk11From860 MaximumCall621Via595Chunk12From860 MaximumCall621Via595Chunk13From860 MaximumCall621Via595Chunk14From860 MaximumCall621Via595Chunk15From860 MaximumCall621Via595Chunk16From860 MaximumCall621Via595Chunk17From860 MaximumCall621Via595Chunk18From860 MaximumCall621Via595Chunk19From860.

Definition values :=
  MaximumCall621Via595Chunk00From860.values ++
  MaximumCall621Via595Chunk01From860.values ++
  MaximumCall621Via595Chunk02From860.values ++
  MaximumCall621Via595Chunk03From860.values ++
  MaximumCall621Via595Chunk04From860.values ++
  MaximumCall621Via595Chunk05From860.values ++
  MaximumCall621Via595Chunk06From860.values ++
  MaximumCall621Via595Chunk07From860.values ++
  MaximumCall621Via595Chunk08From860.values ++
  MaximumCall621Via595Chunk09From860.values ++
  MaximumCall621Via595Chunk10From860.values ++
  MaximumCall621Via595Chunk11From860.values ++
  MaximumCall621Via595Chunk12From860.values ++
  MaximumCall621Via595Chunk13From860.values ++
  MaximumCall621Via595Chunk14From860.values ++
  MaximumCall621Via595Chunk15From860.values ++
  MaximumCall621Via595Chunk16From860.values ++
  MaximumCall621Via595Chunk17From860.values ++
  MaximumCall621Via595Chunk18From860.values ++
  MaximumCall621Via595Chunk19From860.values.

Lemma values_eq :
  List.map MaximumCall621Via595ContextFrom860.depth MaximumCall621Via595ContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 20
    MaximumCall621Via595ContextFrom860.depth MaximumCall621Via595ContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall621Via595Chunk00From860.values_eq,
      MaximumCall621Via595Chunk01From860.values_eq,
      MaximumCall621Via595Chunk02From860.values_eq,
      MaximumCall621Via595Chunk03From860.values_eq,
      MaximumCall621Via595Chunk04From860.values_eq,
      MaximumCall621Via595Chunk05From860.values_eq,
      MaximumCall621Via595Chunk06From860.values_eq,
      MaximumCall621Via595Chunk07From860.values_eq,
      MaximumCall621Via595Chunk08From860.values_eq,
      MaximumCall621Via595Chunk09From860.values_eq,
      MaximumCall621Via595Chunk10From860.values_eq,
      MaximumCall621Via595Chunk11From860.values_eq,
      MaximumCall621Via595Chunk12From860.values_eq,
      MaximumCall621Via595Chunk13From860.values_eq,
      MaximumCall621Via595Chunk14From860.values_eq,
      MaximumCall621Via595Chunk15From860.values_eq,
      MaximumCall621Via595Chunk16From860.values_eq,
      MaximumCall621Via595Chunk17From860.values_eq,
      MaximumCall621Via595Chunk18From860.values_eq,
      MaximumCall621Via595Chunk19From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
