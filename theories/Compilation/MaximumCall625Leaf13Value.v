From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall625Leaf13Context MaximumCall625Leaf13Chunk00 MaximumCall625Leaf13Chunk01 MaximumCall625Leaf13Chunk02 MaximumCall625Leaf13Chunk03 MaximumCall625Leaf13Chunk04 MaximumCall625Leaf13Chunk05.

Definition values :=
  MaximumCall625Leaf13Chunk00.values ++
  MaximumCall625Leaf13Chunk01.values ++
  MaximumCall625Leaf13Chunk02.values ++
  MaximumCall625Leaf13Chunk03.values ++
  MaximumCall625Leaf13Chunk04.values ++
  MaximumCall625Leaf13Chunk05.values.

Lemma values_eq :
  List.map MaximumCall625Leaf13Context.depth MaximumCall625Leaf13Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 6
    MaximumCall625Leaf13Context.depth MaximumCall625Leaf13Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall625Leaf13Chunk00.values_eq,
      MaximumCall625Leaf13Chunk01.values_eq,
      MaximumCall625Leaf13Chunk02.values_eq,
      MaximumCall625Leaf13Chunk03.values_eq,
      MaximumCall625Leaf13Chunk04.values_eq,
      MaximumCall625Leaf13Chunk05.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
