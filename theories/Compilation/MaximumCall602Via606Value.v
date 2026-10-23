From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall602Via606Context MaximumCall602Via606Chunk00 MaximumCall602Via606Chunk01.

Definition values :=
  MaximumCall602Via606Chunk00.values ++
  MaximumCall602Via606Chunk01.values.

Lemma values_eq :
  List.map MaximumCall602Via606Context.depth MaximumCall602Via606Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 2
    MaximumCall602Via606Context.depth MaximumCall602Via606Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall602Via606Chunk00.values_eq,
      MaximumCall602Via606Chunk01.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
