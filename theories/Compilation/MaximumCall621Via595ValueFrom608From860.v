From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall621Via595ContextFrom608From860 MaximumCall621Via595Chunk00From608From860 MaximumCall621Via595Chunk01From608From860 MaximumCall621Via595Chunk02From608From860 MaximumCall621Via595Chunk03From608From860 MaximumCall621Via595Chunk04From608From860 MaximumCall621Via595Chunk05From608From860 MaximumCall621Via595Chunk06From608From860 MaximumCall621Via595Chunk07From608From860 MaximumCall621Via595Chunk08From608From860 MaximumCall621Via595Chunk09From608From860 MaximumCall621Via595Chunk10From608From860 MaximumCall621Via595Chunk11From608From860 MaximumCall621Via595Chunk12From608From860 MaximumCall621Via595Chunk13From608From860 MaximumCall621Via595Chunk14From608From860 MaximumCall621Via595Chunk15From608From860 MaximumCall621Via595Chunk16From608From860 MaximumCall621Via595Chunk17From608From860 MaximumCall621Via595Chunk18From608From860 MaximumCall621Via595Chunk19From608From860.

Definition values :=
  MaximumCall621Via595Chunk00From608From860.values ++
  MaximumCall621Via595Chunk01From608From860.values ++
  MaximumCall621Via595Chunk02From608From860.values ++
  MaximumCall621Via595Chunk03From608From860.values ++
  MaximumCall621Via595Chunk04From608From860.values ++
  MaximumCall621Via595Chunk05From608From860.values ++
  MaximumCall621Via595Chunk06From608From860.values ++
  MaximumCall621Via595Chunk07From608From860.values ++
  MaximumCall621Via595Chunk08From608From860.values ++
  MaximumCall621Via595Chunk09From608From860.values ++
  MaximumCall621Via595Chunk10From608From860.values ++
  MaximumCall621Via595Chunk11From608From860.values ++
  MaximumCall621Via595Chunk12From608From860.values ++
  MaximumCall621Via595Chunk13From608From860.values ++
  MaximumCall621Via595Chunk14From608From860.values ++
  MaximumCall621Via595Chunk15From608From860.values ++
  MaximumCall621Via595Chunk16From608From860.values ++
  MaximumCall621Via595Chunk17From608From860.values ++
  MaximumCall621Via595Chunk18From608From860.values ++
  MaximumCall621Via595Chunk19From608From860.values.

Lemma values_eq :
  List.map MaximumCall621Via595ContextFrom608From860.depth MaximumCall621Via595ContextFrom608From860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 20
    MaximumCall621Via595ContextFrom608From860.depth MaximumCall621Via595ContextFrom608From860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall621Via595Chunk00From608From860.values_eq,
      MaximumCall621Via595Chunk01From608From860.values_eq,
      MaximumCall621Via595Chunk02From608From860.values_eq,
      MaximumCall621Via595Chunk03From608From860.values_eq,
      MaximumCall621Via595Chunk04From608From860.values_eq,
      MaximumCall621Via595Chunk05From608From860.values_eq,
      MaximumCall621Via595Chunk06From608From860.values_eq,
      MaximumCall621Via595Chunk07From608From860.values_eq,
      MaximumCall621Via595Chunk08From608From860.values_eq,
      MaximumCall621Via595Chunk09From608From860.values_eq,
      MaximumCall621Via595Chunk10From608From860.values_eq,
      MaximumCall621Via595Chunk11From608From860.values_eq,
      MaximumCall621Via595Chunk12From608From860.values_eq,
      MaximumCall621Via595Chunk13From608From860.values_eq,
      MaximumCall621Via595Chunk14From608From860.values_eq,
      MaximumCall621Via595Chunk15From608From860.values_eq,
      MaximumCall621Via595Chunk16From608From860.values_eq,
      MaximumCall621Via595Chunk17From608From860.values_eq,
      MaximumCall621Via595Chunk18From608From860.values_eq,
      MaximumCall621Via595Chunk19From608From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
