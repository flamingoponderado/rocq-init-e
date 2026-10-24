From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall625Leaf13ContextFrom860 MaximumCall625Leaf13Chunk00From860 MaximumCall625Leaf13Chunk01From860 MaximumCall625Leaf13Chunk02From860 MaximumCall625Leaf13Chunk03From860 MaximumCall625Leaf13Chunk04From860 MaximumCall625Leaf13Chunk05From860.

Definition values :=
  MaximumCall625Leaf13Chunk00From860.values ++
  MaximumCall625Leaf13Chunk01From860.values ++
  MaximumCall625Leaf13Chunk02From860.values ++
  MaximumCall625Leaf13Chunk03From860.values ++
  MaximumCall625Leaf13Chunk04From860.values ++
  MaximumCall625Leaf13Chunk05From860.values.

Lemma values_eq :
  List.map MaximumCall625Leaf13ContextFrom860.depth MaximumCall625Leaf13ContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 6
    MaximumCall625Leaf13ContextFrom860.depth MaximumCall625Leaf13ContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall625Leaf13Chunk00From860.values_eq,
      MaximumCall625Leaf13Chunk01From860.values_eq,
      MaximumCall625Leaf13Chunk02From860.values_eq,
      MaximumCall625Leaf13Chunk03From860.values_eq,
      MaximumCall625Leaf13Chunk04From860.values_eq,
      MaximumCall625Leaf13Chunk05From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
