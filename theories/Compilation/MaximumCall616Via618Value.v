From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall616Via618Context MaximumCall616Via618Chunk00 MaximumCall616Via618Chunk01 MaximumCall616Via618Chunk02 MaximumCall616Via618Chunk03 MaximumCall616Via618Chunk04 MaximumCall616Via618Chunk05 MaximumCall616Via618Chunk06 MaximumCall616Via618Chunk07 MaximumCall616Via618Chunk08 MaximumCall616Via618Chunk09 MaximumCall616Via618Chunk10 MaximumCall616Via618Chunk11 MaximumCall616Via618Chunk12 MaximumCall616Via618Chunk13 MaximumCall616Via618Chunk14 MaximumCall616Via618Chunk15 MaximumCall616Via618Chunk16.

Definition values :=
  MaximumCall616Via618Chunk00.values ++
  MaximumCall616Via618Chunk01.values ++
  MaximumCall616Via618Chunk02.values ++
  MaximumCall616Via618Chunk03.values ++
  MaximumCall616Via618Chunk04.values ++
  MaximumCall616Via618Chunk05.values ++
  MaximumCall616Via618Chunk06.values ++
  MaximumCall616Via618Chunk07.values ++
  MaximumCall616Via618Chunk08.values ++
  MaximumCall616Via618Chunk09.values ++
  MaximumCall616Via618Chunk10.values ++
  MaximumCall616Via618Chunk11.values ++
  MaximumCall616Via618Chunk12.values ++
  MaximumCall616Via618Chunk13.values ++
  MaximumCall616Via618Chunk14.values ++
  MaximumCall616Via618Chunk15.values ++
  MaximumCall616Via618Chunk16.values.

Lemma values_eq :
  List.map MaximumCall616Via618Context.depth MaximumCall616Via618Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 17
    MaximumCall616Via618Context.depth MaximumCall616Via618Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall616Via618Chunk00.values_eq,
      MaximumCall616Via618Chunk01.values_eq,
      MaximumCall616Via618Chunk02.values_eq,
      MaximumCall616Via618Chunk03.values_eq,
      MaximumCall616Via618Chunk04.values_eq,
      MaximumCall616Via618Chunk05.values_eq,
      MaximumCall616Via618Chunk06.values_eq,
      MaximumCall616Via618Chunk07.values_eq,
      MaximumCall616Via618Chunk08.values_eq,
      MaximumCall616Via618Chunk09.values_eq,
      MaximumCall616Via618Chunk10.values_eq,
      MaximumCall616Via618Chunk11.values_eq,
      MaximumCall616Via618Chunk12.values_eq,
      MaximumCall616Via618Chunk13.values_eq,
      MaximumCall616Via618Chunk14.values_eq,
      MaximumCall616Via618Chunk15.values_eq,
      MaximumCall616Via618Chunk16.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
