From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall869TailContext MaximumCall869TailChunk00.

Definition values :=
  MaximumCall869TailChunk00.values.

Lemma values_eq :
  List.map MaximumCall869TailContext.depth MaximumCall869TailContext.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 1
    MaximumCall869TailContext.depth MaximumCall869TailContext.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall869TailChunk00.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
