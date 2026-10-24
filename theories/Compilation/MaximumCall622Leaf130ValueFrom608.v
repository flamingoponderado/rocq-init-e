From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall622Leaf130ContextFrom608 MaximumCall622Leaf130Chunk00From608 MaximumCall622Leaf130Chunk01From608 MaximumCall622Leaf130Chunk02From608 MaximumCall622Leaf130Chunk03From608 MaximumCall622Leaf130Chunk04From608 MaximumCall622Leaf130Chunk05From608 MaximumCall622Leaf130Chunk06From608 MaximumCall622Leaf130Chunk07From608.

Definition values :=
  MaximumCall622Leaf130Chunk00From608.values ++
  MaximumCall622Leaf130Chunk01From608.values ++
  MaximumCall622Leaf130Chunk02From608.values ++
  MaximumCall622Leaf130Chunk03From608.values ++
  MaximumCall622Leaf130Chunk04From608.values ++
  MaximumCall622Leaf130Chunk05From608.values ++
  MaximumCall622Leaf130Chunk06From608.values ++
  MaximumCall622Leaf130Chunk07From608.values.

Lemma values_eq :
  List.map MaximumCall622Leaf130ContextFrom608.depth MaximumCall622Leaf130ContextFrom608.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 8
    MaximumCall622Leaf130ContextFrom608.depth MaximumCall622Leaf130ContextFrom608.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall622Leaf130Chunk00From608.values_eq,
      MaximumCall622Leaf130Chunk01From608.values_eq,
      MaximumCall622Leaf130Chunk02From608.values_eq,
      MaximumCall622Leaf130Chunk03From608.values_eq,
      MaximumCall622Leaf130Chunk04From608.values_eq,
      MaximumCall622Leaf130Chunk05From608.values_eq,
      MaximumCall622Leaf130Chunk06From608.values_eq,
      MaximumCall622Leaf130Chunk07From608.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
