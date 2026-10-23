From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall621Leaf148Context MaximumCall621Leaf148Chunk00 MaximumCall621Leaf148Chunk01 MaximumCall621Leaf148Chunk02 MaximumCall621Leaf148Chunk03 MaximumCall621Leaf148Chunk04 MaximumCall621Leaf148Chunk05 MaximumCall621Leaf148Chunk06 MaximumCall621Leaf148Chunk07 MaximumCall621Leaf148Chunk08.

Definition values :=
  MaximumCall621Leaf148Chunk00.values ++
  MaximumCall621Leaf148Chunk01.values ++
  MaximumCall621Leaf148Chunk02.values ++
  MaximumCall621Leaf148Chunk03.values ++
  MaximumCall621Leaf148Chunk04.values ++
  MaximumCall621Leaf148Chunk05.values ++
  MaximumCall621Leaf148Chunk06.values ++
  MaximumCall621Leaf148Chunk07.values ++
  MaximumCall621Leaf148Chunk08.values.

Lemma values_eq :
  List.map MaximumCall621Leaf148Context.depth MaximumCall621Leaf148Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 9
    MaximumCall621Leaf148Context.depth MaximumCall621Leaf148Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall621Leaf148Chunk00.values_eq,
      MaximumCall621Leaf148Chunk01.values_eq,
      MaximumCall621Leaf148Chunk02.values_eq,
      MaximumCall621Leaf148Chunk03.values_eq,
      MaximumCall621Leaf148Chunk04.values_eq,
      MaximumCall621Leaf148Chunk05.values_eq,
      MaximumCall621Leaf148Chunk06.values_eq,
      MaximumCall621Leaf148Chunk07.values_eq,
      MaximumCall621Leaf148Chunk08.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
