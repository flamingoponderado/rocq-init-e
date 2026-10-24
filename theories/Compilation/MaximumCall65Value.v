From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall65Context MaximumCall65Chunk00 MaximumCall65Chunk01 MaximumCall65Chunk02 MaximumCall65Chunk03 MaximumCall65Chunk04 MaximumCall65Chunk05 MaximumCall65Chunk06 MaximumCall65Chunk07 MaximumCall65Chunk08 MaximumCall65Chunk09 MaximumCall65Chunk10 MaximumCall65Chunk11.

Definition values :=
  MaximumCall65Chunk00.values ++
  MaximumCall65Chunk01.values ++
  MaximumCall65Chunk02.values ++
  MaximumCall65Chunk03.values ++
  MaximumCall65Chunk04.values ++
  MaximumCall65Chunk05.values ++
  MaximumCall65Chunk06.values ++
  MaximumCall65Chunk07.values ++
  MaximumCall65Chunk08.values ++
  MaximumCall65Chunk09.values ++
  MaximumCall65Chunk10.values ++
  MaximumCall65Chunk11.values.

Lemma values_eq :
  List.map MaximumCall65Context.depth MaximumCall65Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 12
    MaximumCall65Context.depth MaximumCall65Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall65Chunk00.values_eq,
      MaximumCall65Chunk01.values_eq,
      MaximumCall65Chunk02.values_eq,
      MaximumCall65Chunk03.values_eq,
      MaximumCall65Chunk04.values_eq,
      MaximumCall65Chunk05.values_eq,
      MaximumCall65Chunk06.values_eq,
      MaximumCall65Chunk07.values_eq,
      MaximumCall65Chunk08.values_eq,
      MaximumCall65Chunk09.values_eq,
      MaximumCall65Chunk10.values_eq,
      MaximumCall65Chunk11.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
