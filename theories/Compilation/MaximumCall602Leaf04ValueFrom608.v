From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall602Leaf04ContextFrom608 MaximumCall602Leaf04Chunk00From608 MaximumCall602Leaf04Chunk01From608 MaximumCall602Leaf04Chunk02From608 MaximumCall602Leaf04Chunk03From608 MaximumCall602Leaf04Chunk04From608 MaximumCall602Leaf04Chunk05From608 MaximumCall602Leaf04Chunk06From608 MaximumCall602Leaf04Chunk07From608 MaximumCall602Leaf04Chunk08From608 MaximumCall602Leaf04Chunk09From608 MaximumCall602Leaf04Chunk10From608.

Definition values :=
  MaximumCall602Leaf04Chunk00From608.values ++
  MaximumCall602Leaf04Chunk01From608.values ++
  MaximumCall602Leaf04Chunk02From608.values ++
  MaximumCall602Leaf04Chunk03From608.values ++
  MaximumCall602Leaf04Chunk04From608.values ++
  MaximumCall602Leaf04Chunk05From608.values ++
  MaximumCall602Leaf04Chunk06From608.values ++
  MaximumCall602Leaf04Chunk07From608.values ++
  MaximumCall602Leaf04Chunk08From608.values ++
  MaximumCall602Leaf04Chunk09From608.values ++
  MaximumCall602Leaf04Chunk10From608.values.

Lemma values_eq :
  List.map MaximumCall602Leaf04ContextFrom608.depth MaximumCall602Leaf04ContextFrom608.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 11
    MaximumCall602Leaf04ContextFrom608.depth MaximumCall602Leaf04ContextFrom608.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall602Leaf04Chunk00From608.values_eq,
      MaximumCall602Leaf04Chunk01From608.values_eq,
      MaximumCall602Leaf04Chunk02From608.values_eq,
      MaximumCall602Leaf04Chunk03From608.values_eq,
      MaximumCall602Leaf04Chunk04From608.values_eq,
      MaximumCall602Leaf04Chunk05From608.values_eq,
      MaximumCall602Leaf04Chunk06From608.values_eq,
      MaximumCall602Leaf04Chunk07From608.values_eq,
      MaximumCall602Leaf04Chunk08From608.values_eq,
      MaximumCall602Leaf04Chunk09From608.values_eq,
      MaximumCall602Leaf04Chunk10From608.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
