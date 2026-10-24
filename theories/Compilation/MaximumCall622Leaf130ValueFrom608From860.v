From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall622Leaf130ContextFrom608From860 MaximumCall622Leaf130Chunk00From608From860 MaximumCall622Leaf130Chunk01From608From860 MaximumCall622Leaf130Chunk02From608From860 MaximumCall622Leaf130Chunk03From608From860 MaximumCall622Leaf130Chunk04From608From860 MaximumCall622Leaf130Chunk05From608From860 MaximumCall622Leaf130Chunk06From608From860 MaximumCall622Leaf130Chunk07From608From860.

Definition values :=
  MaximumCall622Leaf130Chunk00From608From860.values ++
  MaximumCall622Leaf130Chunk01From608From860.values ++
  MaximumCall622Leaf130Chunk02From608From860.values ++
  MaximumCall622Leaf130Chunk03From608From860.values ++
  MaximumCall622Leaf130Chunk04From608From860.values ++
  MaximumCall622Leaf130Chunk05From608From860.values ++
  MaximumCall622Leaf130Chunk06From608From860.values ++
  MaximumCall622Leaf130Chunk07From608From860.values.

Lemma values_eq :
  List.map MaximumCall622Leaf130ContextFrom608From860.depth MaximumCall622Leaf130ContextFrom608From860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 8
    MaximumCall622Leaf130ContextFrom608From860.depth MaximumCall622Leaf130ContextFrom608From860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall622Leaf130Chunk00From608From860.values_eq,
      MaximumCall622Leaf130Chunk01From608From860.values_eq,
      MaximumCall622Leaf130Chunk02From608From860.values_eq,
      MaximumCall622Leaf130Chunk03From608From860.values_eq,
      MaximumCall622Leaf130Chunk04From608From860.values_eq,
      MaximumCall622Leaf130Chunk05From608From860.values_eq,
      MaximumCall622Leaf130Chunk06From608From860.values_eq,
      MaximumCall622Leaf130Chunk07From608From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
