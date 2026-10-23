From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall603Via619From622Context MaximumCall603Via619From622Chunk00 MaximumCall603Via619From622Chunk01 MaximumCall603Via619From622Chunk02 MaximumCall603Via619From622Chunk03 MaximumCall603Via619From622Chunk04 MaximumCall603Via619From622Chunk05 MaximumCall603Via619From622Chunk06 MaximumCall603Via619From622Chunk07 MaximumCall603Via619From622Chunk08.

Definition values :=
  MaximumCall603Via619From622Chunk00.values ++
  MaximumCall603Via619From622Chunk01.values ++
  MaximumCall603Via619From622Chunk02.values ++
  MaximumCall603Via619From622Chunk03.values ++
  MaximumCall603Via619From622Chunk04.values ++
  MaximumCall603Via619From622Chunk05.values ++
  MaximumCall603Via619From622Chunk06.values ++
  MaximumCall603Via619From622Chunk07.values ++
  MaximumCall603Via619From622Chunk08.values.

Lemma values_eq :
  List.map MaximumCall603Via619From622Context.depth MaximumCall603Via619From622Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 9
    MaximumCall603Via619From622Context.depth MaximumCall603Via619From622Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall603Via619From622Chunk00.values_eq,
      MaximumCall603Via619From622Chunk01.values_eq,
      MaximumCall603Via619From622Chunk02.values_eq,
      MaximumCall603Via619From622Chunk03.values_eq,
      MaximumCall603Via619From622Chunk04.values_eq,
      MaximumCall603Via619From622Chunk05.values_eq,
      MaximumCall603Via619From622Chunk06.values_eq,
      MaximumCall603Via619From622Chunk07.values_eq,
      MaximumCall603Via619From622Chunk08.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
