From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall625Via860Context MaximumCall625Via860Chunk00 MaximumCall625Via860Chunk01 MaximumCall625Via860Chunk02 MaximumCall625Via860Chunk03 MaximumCall625Via860Chunk04 MaximumCall625Via860Chunk05 MaximumCall625Via860Chunk06 MaximumCall625Via860Chunk07 MaximumCall625Via860Chunk08 MaximumCall625Via860Chunk09.

Definition values :=
  MaximumCall625Via860Chunk00.values ++
  MaximumCall625Via860Chunk01.values ++
  MaximumCall625Via860Chunk02.values ++
  MaximumCall625Via860Chunk03.values ++
  MaximumCall625Via860Chunk04.values ++
  MaximumCall625Via860Chunk05.values ++
  MaximumCall625Via860Chunk06.values ++
  MaximumCall625Via860Chunk07.values ++
  MaximumCall625Via860Chunk08.values ++
  MaximumCall625Via860Chunk09.values.

Lemma values_eq :
  List.map MaximumCall625Via860Context.depth MaximumCall625Via860Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 10
    MaximumCall625Via860Context.depth MaximumCall625Via860Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall625Via860Chunk00.values_eq,
      MaximumCall625Via860Chunk01.values_eq,
      MaximumCall625Via860Chunk02.values_eq,
      MaximumCall625Via860Chunk03.values_eq,
      MaximumCall625Via860Chunk04.values_eq,
      MaximumCall625Via860Chunk05.values_eq,
      MaximumCall625Via860Chunk06.values_eq,
      MaximumCall625Via860Chunk07.values_eq,
      MaximumCall625Via860Chunk08.values_eq,
      MaximumCall625Via860Chunk09.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
