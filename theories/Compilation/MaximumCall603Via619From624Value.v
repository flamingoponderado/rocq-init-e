From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall603Via619From624Context MaximumCall603Via619From624Chunk00 MaximumCall603Via619From624Chunk01 MaximumCall603Via619From624Chunk02 MaximumCall603Via619From624Chunk03 MaximumCall603Via619From624Chunk04 MaximumCall603Via619From624Chunk05 MaximumCall603Via619From624Chunk06 MaximumCall603Via619From624Chunk07 MaximumCall603Via619From624Chunk08.

Definition values :=
  MaximumCall603Via619From624Chunk00.values ++
  MaximumCall603Via619From624Chunk01.values ++
  MaximumCall603Via619From624Chunk02.values ++
  MaximumCall603Via619From624Chunk03.values ++
  MaximumCall603Via619From624Chunk04.values ++
  MaximumCall603Via619From624Chunk05.values ++
  MaximumCall603Via619From624Chunk06.values ++
  MaximumCall603Via619From624Chunk07.values ++
  MaximumCall603Via619From624Chunk08.values.

Lemma values_eq :
  List.map MaximumCall603Via619From624Context.depth MaximumCall603Via619From624Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 9
    MaximumCall603Via619From624Context.depth MaximumCall603Via619From624Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall603Via619From624Chunk00.values_eq,
      MaximumCall603Via619From624Chunk01.values_eq,
      MaximumCall603Via619From624Chunk02.values_eq,
      MaximumCall603Via619From624Chunk03.values_eq,
      MaximumCall603Via619From624Chunk04.values_eq,
      MaximumCall603Via619From624Chunk05.values_eq,
      MaximumCall603Via619From624Chunk06.values_eq,
      MaximumCall603Via619From624Chunk07.values_eq,
      MaximumCall603Via619From624Chunk08.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
