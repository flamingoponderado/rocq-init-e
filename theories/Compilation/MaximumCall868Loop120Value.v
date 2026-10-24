From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall868Loop120Context MaximumCall868Loop120Chunk00 MaximumCall868Loop120Chunk01 MaximumCall868Loop120Chunk02 MaximumCall868Loop120Chunk03.

Definition values :=
  MaximumCall868Loop120Chunk00.values ++
  MaximumCall868Loop120Chunk01.values ++
  MaximumCall868Loop120Chunk02.values ++
  MaximumCall868Loop120Chunk03.values.

Lemma values_eq :
  List.map MaximumCall868Loop120Context.depth MaximumCall868Loop120Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 4
    MaximumCall868Loop120Context.depth MaximumCall868Loop120Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall868Loop120Chunk00.values_eq,
      MaximumCall868Loop120Chunk01.values_eq,
      MaximumCall868Loop120Chunk02.values_eq,
      MaximumCall868Loop120Chunk03.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
