From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall387Via868Context MaximumCall387Via868Chunk00 MaximumCall387Via868Chunk01 MaximumCall387Via868Chunk02 MaximumCall387Via868Chunk03 MaximumCall387Via868Chunk04 MaximumCall387Via868Chunk05 MaximumCall387Via868Chunk06 MaximumCall387Via868Chunk07 MaximumCall387Via868Chunk08 MaximumCall387Via868Chunk09 MaximumCall387Via868Chunk10 MaximumCall387Via868Chunk11 MaximumCall387Via868Chunk12 MaximumCall387Via868Chunk13 MaximumCall387Via868Chunk14 MaximumCall387Via868Chunk15.

Definition values :=
  MaximumCall387Via868Chunk00.values ++
  MaximumCall387Via868Chunk01.values ++
  MaximumCall387Via868Chunk02.values ++
  MaximumCall387Via868Chunk03.values ++
  MaximumCall387Via868Chunk04.values ++
  MaximumCall387Via868Chunk05.values ++
  MaximumCall387Via868Chunk06.values ++
  MaximumCall387Via868Chunk07.values ++
  MaximumCall387Via868Chunk08.values ++
  MaximumCall387Via868Chunk09.values ++
  MaximumCall387Via868Chunk10.values ++
  MaximumCall387Via868Chunk11.values ++
  MaximumCall387Via868Chunk12.values ++
  MaximumCall387Via868Chunk13.values ++
  MaximumCall387Via868Chunk14.values ++
  MaximumCall387Via868Chunk15.values.

Lemma values_eq :
  List.map MaximumCall387Via868Context.depth MaximumCall387Via868Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 16
    MaximumCall387Via868Context.depth MaximumCall387Via868Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall387Via868Chunk00.values_eq,
      MaximumCall387Via868Chunk01.values_eq,
      MaximumCall387Via868Chunk02.values_eq,
      MaximumCall387Via868Chunk03.values_eq,
      MaximumCall387Via868Chunk04.values_eq,
      MaximumCall387Via868Chunk05.values_eq,
      MaximumCall387Via868Chunk06.values_eq,
      MaximumCall387Via868Chunk07.values_eq,
      MaximumCall387Via868Chunk08.values_eq,
      MaximumCall387Via868Chunk09.values_eq,
      MaximumCall387Via868Chunk10.values_eq,
      MaximumCall387Via868Chunk11.values_eq,
      MaximumCall387Via868Chunk12.values_eq,
      MaximumCall387Via868Chunk13.values_eq,
      MaximumCall387Via868Chunk14.values_eq,
      MaximumCall387Via868Chunk15.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
