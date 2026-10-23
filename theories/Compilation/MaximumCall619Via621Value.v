From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall619Via621Context MaximumCall619Via621Chunk00 MaximumCall619Via621Chunk01 MaximumCall619Via621Chunk02 MaximumCall619Via621Chunk03 MaximumCall619Via621Chunk04 MaximumCall619Via621Chunk05.

Definition values :=
  MaximumCall619Via621Chunk00.values ++
  MaximumCall619Via621Chunk01.values ++
  MaximumCall619Via621Chunk02.values ++
  MaximumCall619Via621Chunk03.values ++
  MaximumCall619Via621Chunk04.values ++
  MaximumCall619Via621Chunk05.values.

Lemma values_eq :
  List.map MaximumCall619Via621Context.depth MaximumCall619Via621Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 6
    MaximumCall619Via621Context.depth MaximumCall619Via621Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall619Via621Chunk00.values_eq,
      MaximumCall619Via621Chunk01.values_eq,
      MaximumCall619Via621Chunk02.values_eq,
      MaximumCall619Via621Chunk03.values_eq,
      MaximumCall619Via621Chunk04.values_eq,
      MaximumCall619Via621Chunk05.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
