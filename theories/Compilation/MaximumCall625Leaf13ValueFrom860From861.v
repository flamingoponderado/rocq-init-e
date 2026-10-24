From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall625Leaf13ContextFrom860From861 MaximumCall625Leaf13Chunk00From860From861 MaximumCall625Leaf13Chunk01From860From861 MaximumCall625Leaf13Chunk02From860From861 MaximumCall625Leaf13Chunk03From860From861 MaximumCall625Leaf13Chunk04From860From861 MaximumCall625Leaf13Chunk05From860From861.

Definition values :=
  MaximumCall625Leaf13Chunk00From860From861.values ++
  MaximumCall625Leaf13Chunk01From860From861.values ++
  MaximumCall625Leaf13Chunk02From860From861.values ++
  MaximumCall625Leaf13Chunk03From860From861.values ++
  MaximumCall625Leaf13Chunk04From860From861.values ++
  MaximumCall625Leaf13Chunk05From860From861.values.

Lemma values_eq :
  List.map MaximumCall625Leaf13ContextFrom860From861.depth MaximumCall625Leaf13ContextFrom860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 6
    MaximumCall625Leaf13ContextFrom860From861.depth MaximumCall625Leaf13ContextFrom860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall625Leaf13Chunk00From860From861.values_eq,
      MaximumCall625Leaf13Chunk01From860From861.values_eq,
      MaximumCall625Leaf13Chunk02From860From861.values_eq,
      MaximumCall625Leaf13Chunk03From860From861.values_eq,
      MaximumCall625Leaf13Chunk04From860From861.values_eq,
      MaximumCall625Leaf13Chunk05From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
