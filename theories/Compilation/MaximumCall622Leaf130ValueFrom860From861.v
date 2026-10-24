From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall622Leaf130ContextFrom860From861 MaximumCall622Leaf130Chunk00From860From861 MaximumCall622Leaf130Chunk01From860From861 MaximumCall622Leaf130Chunk02From860From861 MaximumCall622Leaf130Chunk03From860From861 MaximumCall622Leaf130Chunk04From860From861 MaximumCall622Leaf130Chunk05From860From861 MaximumCall622Leaf130Chunk06From860From861 MaximumCall622Leaf130Chunk07From860From861.

Definition values :=
  MaximumCall622Leaf130Chunk00From860From861.values ++
  MaximumCall622Leaf130Chunk01From860From861.values ++
  MaximumCall622Leaf130Chunk02From860From861.values ++
  MaximumCall622Leaf130Chunk03From860From861.values ++
  MaximumCall622Leaf130Chunk04From860From861.values ++
  MaximumCall622Leaf130Chunk05From860From861.values ++
  MaximumCall622Leaf130Chunk06From860From861.values ++
  MaximumCall622Leaf130Chunk07From860From861.values.

Lemma values_eq :
  List.map MaximumCall622Leaf130ContextFrom860From861.depth MaximumCall622Leaf130ContextFrom860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 8
    MaximumCall622Leaf130ContextFrom860From861.depth MaximumCall622Leaf130ContextFrom860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall622Leaf130Chunk00From860From861.values_eq,
      MaximumCall622Leaf130Chunk01From860From861.values_eq,
      MaximumCall622Leaf130Chunk02From860From861.values_eq,
      MaximumCall622Leaf130Chunk03From860From861.values_eq,
      MaximumCall622Leaf130Chunk04From860From861.values_eq,
      MaximumCall622Leaf130Chunk05From860From861.values_eq,
      MaximumCall622Leaf130Chunk06From860From861.values_eq,
      MaximumCall622Leaf130Chunk07From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
