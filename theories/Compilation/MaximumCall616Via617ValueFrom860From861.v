From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall616Via617ContextFrom860From861 MaximumCall616Via617Chunk00From860From861 MaximumCall616Via617Chunk01From860From861 MaximumCall616Via617Chunk02From860From861 MaximumCall616Via617Chunk03From860From861 MaximumCall616Via617Chunk04From860From861 MaximumCall616Via617Chunk05From860From861 MaximumCall616Via617Chunk06From860From861 MaximumCall616Via617Chunk07From860From861 MaximumCall616Via617Chunk08From860From861 MaximumCall616Via617Chunk09From860From861 MaximumCall616Via617Chunk10From860From861 MaximumCall616Via617Chunk11From860From861 MaximumCall616Via617Chunk12From860From861 MaximumCall616Via617Chunk13From860From861 MaximumCall616Via617Chunk14From860From861 MaximumCall616Via617Chunk15From860From861 MaximumCall616Via617Chunk16From860From861.

Definition values :=
  MaximumCall616Via617Chunk00From860From861.values ++
  MaximumCall616Via617Chunk01From860From861.values ++
  MaximumCall616Via617Chunk02From860From861.values ++
  MaximumCall616Via617Chunk03From860From861.values ++
  MaximumCall616Via617Chunk04From860From861.values ++
  MaximumCall616Via617Chunk05From860From861.values ++
  MaximumCall616Via617Chunk06From860From861.values ++
  MaximumCall616Via617Chunk07From860From861.values ++
  MaximumCall616Via617Chunk08From860From861.values ++
  MaximumCall616Via617Chunk09From860From861.values ++
  MaximumCall616Via617Chunk10From860From861.values ++
  MaximumCall616Via617Chunk11From860From861.values ++
  MaximumCall616Via617Chunk12From860From861.values ++
  MaximumCall616Via617Chunk13From860From861.values ++
  MaximumCall616Via617Chunk14From860From861.values ++
  MaximumCall616Via617Chunk15From860From861.values ++
  MaximumCall616Via617Chunk16From860From861.values.

Lemma values_eq :
  List.map MaximumCall616Via617ContextFrom860From861.depth MaximumCall616Via617ContextFrom860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 17
    MaximumCall616Via617ContextFrom860From861.depth MaximumCall616Via617ContextFrom860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall616Via617Chunk00From860From861.values_eq,
      MaximumCall616Via617Chunk01From860From861.values_eq,
      MaximumCall616Via617Chunk02From860From861.values_eq,
      MaximumCall616Via617Chunk03From860From861.values_eq,
      MaximumCall616Via617Chunk04From860From861.values_eq,
      MaximumCall616Via617Chunk05From860From861.values_eq,
      MaximumCall616Via617Chunk06From860From861.values_eq,
      MaximumCall616Via617Chunk07From860From861.values_eq,
      MaximumCall616Via617Chunk08From860From861.values_eq,
      MaximumCall616Via617Chunk09From860From861.values_eq,
      MaximumCall616Via617Chunk10From860From861.values_eq,
      MaximumCall616Via617Chunk11From860From861.values_eq,
      MaximumCall616Via617Chunk12From860From861.values_eq,
      MaximumCall616Via617Chunk13From860From861.values_eq,
      MaximumCall616Via617Chunk14From860From861.values_eq,
      MaximumCall616Via617Chunk15From860From861.values_eq,
      MaximumCall616Via617Chunk16From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
