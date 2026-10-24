From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall602Leaf04ContextFrom860From861 MaximumCall602Leaf04Chunk00From860From861 MaximumCall602Leaf04Chunk01From860From861 MaximumCall602Leaf04Chunk02From860From861 MaximumCall602Leaf04Chunk03From860From861 MaximumCall602Leaf04Chunk04From860From861 MaximumCall602Leaf04Chunk05From860From861 MaximumCall602Leaf04Chunk06From860From861 MaximumCall602Leaf04Chunk07From860From861 MaximumCall602Leaf04Chunk08From860From861 MaximumCall602Leaf04Chunk09From860From861 MaximumCall602Leaf04Chunk10From860From861.

Definition values :=
  MaximumCall602Leaf04Chunk00From860From861.values ++
  MaximumCall602Leaf04Chunk01From860From861.values ++
  MaximumCall602Leaf04Chunk02From860From861.values ++
  MaximumCall602Leaf04Chunk03From860From861.values ++
  MaximumCall602Leaf04Chunk04From860From861.values ++
  MaximumCall602Leaf04Chunk05From860From861.values ++
  MaximumCall602Leaf04Chunk06From860From861.values ++
  MaximumCall602Leaf04Chunk07From860From861.values ++
  MaximumCall602Leaf04Chunk08From860From861.values ++
  MaximumCall602Leaf04Chunk09From860From861.values ++
  MaximumCall602Leaf04Chunk10From860From861.values.

Lemma values_eq :
  List.map MaximumCall602Leaf04ContextFrom860From861.depth MaximumCall602Leaf04ContextFrom860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 11
    MaximumCall602Leaf04ContextFrom860From861.depth MaximumCall602Leaf04ContextFrom860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall602Leaf04Chunk00From860From861.values_eq,
      MaximumCall602Leaf04Chunk01From860From861.values_eq,
      MaximumCall602Leaf04Chunk02From860From861.values_eq,
      MaximumCall602Leaf04Chunk03From860From861.values_eq,
      MaximumCall602Leaf04Chunk04From860From861.values_eq,
      MaximumCall602Leaf04Chunk05From860From861.values_eq,
      MaximumCall602Leaf04Chunk06From860From861.values_eq,
      MaximumCall602Leaf04Chunk07From860From861.values_eq,
      MaximumCall602Leaf04Chunk08From860From861.values_eq,
      MaximumCall602Leaf04Chunk09From860From861.values_eq,
      MaximumCall602Leaf04Chunk10From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
