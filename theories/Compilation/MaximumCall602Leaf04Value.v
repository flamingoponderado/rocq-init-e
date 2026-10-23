From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall602Leaf04Context MaximumCall602Leaf04Chunk00 MaximumCall602Leaf04Chunk01 MaximumCall602Leaf04Chunk02 MaximumCall602Leaf04Chunk03 MaximumCall602Leaf04Chunk04 MaximumCall602Leaf04Chunk05 MaximumCall602Leaf04Chunk06 MaximumCall602Leaf04Chunk07 MaximumCall602Leaf04Chunk08 MaximumCall602Leaf04Chunk09 MaximumCall602Leaf04Chunk10.

Definition values :=
  MaximumCall602Leaf04Chunk00.values ++
  MaximumCall602Leaf04Chunk01.values ++
  MaximumCall602Leaf04Chunk02.values ++
  MaximumCall602Leaf04Chunk03.values ++
  MaximumCall602Leaf04Chunk04.values ++
  MaximumCall602Leaf04Chunk05.values ++
  MaximumCall602Leaf04Chunk06.values ++
  MaximumCall602Leaf04Chunk07.values ++
  MaximumCall602Leaf04Chunk08.values ++
  MaximumCall602Leaf04Chunk09.values ++
  MaximumCall602Leaf04Chunk10.values.

Lemma values_eq :
  List.map MaximumCall602Leaf04Context.depth MaximumCall602Leaf04Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 11
    MaximumCall602Leaf04Context.depth MaximumCall602Leaf04Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall602Leaf04Chunk00.values_eq,
      MaximumCall602Leaf04Chunk01.values_eq,
      MaximumCall602Leaf04Chunk02.values_eq,
      MaximumCall602Leaf04Chunk03.values_eq,
      MaximumCall602Leaf04Chunk04.values_eq,
      MaximumCall602Leaf04Chunk05.values_eq,
      MaximumCall602Leaf04Chunk06.values_eq,
      MaximumCall602Leaf04Chunk07.values_eq,
      MaximumCall602Leaf04Chunk08.values_eq,
      MaximumCall602Leaf04Chunk09.values_eq,
      MaximumCall602Leaf04Chunk10.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
