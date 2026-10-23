From Galette Require Import Base.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall78Via625Context MaximumCall78Via625Chunk00
  MaximumCall78Via625Chunk01 MaximumCall78Via625Chunk02.

Definition values :=
  MaximumCall78Via625Chunk00.values ++
  MaximumCall78Via625Chunk01.values ++
  MaximumCall78Via625Chunk02.values.

Lemma values_eq :
  List.map MaximumCall78Via625Context.depth MaximumCall78Via625Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 3
    MaximumCall78Via625Context.depth MaximumCall78Via625Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall78Via625Chunk00.values_eq,
      MaximumCall78Via625Chunk01.values_eq,
      MaximumCall78Via625Chunk02.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
