From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall622Leaf130Context MaximumCall622Leaf130Chunk00 MaximumCall622Leaf130Chunk01 MaximumCall622Leaf130Chunk02 MaximumCall622Leaf130Chunk03 MaximumCall622Leaf130Chunk04 MaximumCall622Leaf130Chunk05 MaximumCall622Leaf130Chunk06 MaximumCall622Leaf130Chunk07.

Definition values :=
  MaximumCall622Leaf130Chunk00.values ++
  MaximumCall622Leaf130Chunk01.values ++
  MaximumCall622Leaf130Chunk02.values ++
  MaximumCall622Leaf130Chunk03.values ++
  MaximumCall622Leaf130Chunk04.values ++
  MaximumCall622Leaf130Chunk05.values ++
  MaximumCall622Leaf130Chunk06.values ++
  MaximumCall622Leaf130Chunk07.values.

Lemma values_eq :
  List.map MaximumCall622Leaf130Context.depth MaximumCall622Leaf130Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 8
    MaximumCall622Leaf130Context.depth MaximumCall622Leaf130Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall622Leaf130Chunk00.values_eq,
      MaximumCall622Leaf130Chunk01.values_eq,
      MaximumCall622Leaf130Chunk02.values_eq,
      MaximumCall622Leaf130Chunk03.values_eq,
      MaximumCall622Leaf130Chunk04.values_eq,
      MaximumCall622Leaf130Chunk05.values_eq,
      MaximumCall622Leaf130Chunk06.values_eq,
      MaximumCall622Leaf130Chunk07.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
