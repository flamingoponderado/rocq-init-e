From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall617Via595Context MaximumCall617Via595Chunk00 MaximumCall617Via595Chunk01 MaximumCall617Via595Chunk02 MaximumCall617Via595Chunk03 MaximumCall617Via595Chunk04 MaximumCall617Via595Chunk05 MaximumCall617Via595Chunk06 MaximumCall617Via595Chunk07 MaximumCall617Via595Chunk08.

Definition values :=
  MaximumCall617Via595Chunk00.values ++
  MaximumCall617Via595Chunk01.values ++
  MaximumCall617Via595Chunk02.values ++
  MaximumCall617Via595Chunk03.values ++
  MaximumCall617Via595Chunk04.values ++
  MaximumCall617Via595Chunk05.values ++
  MaximumCall617Via595Chunk06.values ++
  MaximumCall617Via595Chunk07.values ++
  MaximumCall617Via595Chunk08.values.

Lemma values_eq :
  List.map MaximumCall617Via595Context.depth MaximumCall617Via595Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 9
    MaximumCall617Via595Context.depth MaximumCall617Via595Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall617Via595Chunk00.values_eq,
      MaximumCall617Via595Chunk01.values_eq,
      MaximumCall617Via595Chunk02.values_eq,
      MaximumCall617Via595Chunk03.values_eq,
      MaximumCall617Via595Chunk04.values_eq,
      MaximumCall617Via595Chunk05.values_eq,
      MaximumCall617Via595Chunk06.values_eq,
      MaximumCall617Via595Chunk07.values_eq,
      MaximumCall617Via595Chunk08.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
