From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall615Via618Context MaximumCall615Via618Chunk00 MaximumCall615Via618Chunk01 MaximumCall615Via618Chunk02 MaximumCall615Via618Chunk03 MaximumCall615Via618Chunk04 MaximumCall615Via618Chunk05 MaximumCall615Via618Chunk06.

Definition values :=
  MaximumCall615Via618Chunk00.values ++
  MaximumCall615Via618Chunk01.values ++
  MaximumCall615Via618Chunk02.values ++
  MaximumCall615Via618Chunk03.values ++
  MaximumCall615Via618Chunk04.values ++
  MaximumCall615Via618Chunk05.values ++
  MaximumCall615Via618Chunk06.values.

Lemma values_eq :
  List.map MaximumCall615Via618Context.depth MaximumCall615Via618Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 7
    MaximumCall615Via618Context.depth MaximumCall615Via618Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall615Via618Chunk00.values_eq,
      MaximumCall615Via618Chunk01.values_eq,
      MaximumCall615Via618Chunk02.values_eq,
      MaximumCall615Via618Chunk03.values_eq,
      MaximumCall615Via618Chunk04.values_eq,
      MaximumCall615Via618Chunk05.values_eq,
      MaximumCall615Via618Chunk06.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
