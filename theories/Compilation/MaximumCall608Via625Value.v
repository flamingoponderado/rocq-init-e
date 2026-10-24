From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall608Via625Context MaximumCall608Via625Chunk00 MaximumCall608Via625Chunk01 MaximumCall608Via625Chunk02 MaximumCall608Via625Chunk03.

Definition values :=
  MaximumCall608Via625Chunk00.values ++
  MaximumCall608Via625Chunk01.values ++
  MaximumCall608Via625Chunk02.values ++
  MaximumCall608Via625Chunk03.values.

Lemma values_eq :
  List.map MaximumCall608Via625Context.depth MaximumCall608Via625Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 4
    MaximumCall608Via625Context.depth MaximumCall608Via625Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall608Via625Chunk00.values_eq,
      MaximumCall608Via625Chunk01.values_eq,
      MaximumCall608Via625Chunk02.values_eq,
      MaximumCall608Via625Chunk03.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
