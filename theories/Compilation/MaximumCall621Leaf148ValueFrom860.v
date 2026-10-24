From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall621Leaf148ContextFrom860 MaximumCall621Leaf148Chunk00From860 MaximumCall621Leaf148Chunk01From860 MaximumCall621Leaf148Chunk02From860 MaximumCall621Leaf148Chunk03From860 MaximumCall621Leaf148Chunk04From860 MaximumCall621Leaf148Chunk05From860 MaximumCall621Leaf148Chunk06From860 MaximumCall621Leaf148Chunk07From860 MaximumCall621Leaf148Chunk08From860.

Definition values :=
  MaximumCall621Leaf148Chunk00From860.values ++
  MaximumCall621Leaf148Chunk01From860.values ++
  MaximumCall621Leaf148Chunk02From860.values ++
  MaximumCall621Leaf148Chunk03From860.values ++
  MaximumCall621Leaf148Chunk04From860.values ++
  MaximumCall621Leaf148Chunk05From860.values ++
  MaximumCall621Leaf148Chunk06From860.values ++
  MaximumCall621Leaf148Chunk07From860.values ++
  MaximumCall621Leaf148Chunk08From860.values.

Lemma values_eq :
  List.map MaximumCall621Leaf148ContextFrom860.depth MaximumCall621Leaf148ContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 9
    MaximumCall621Leaf148ContextFrom860.depth MaximumCall621Leaf148ContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall621Leaf148Chunk00From860.values_eq,
      MaximumCall621Leaf148Chunk01From860.values_eq,
      MaximumCall621Leaf148Chunk02From860.values_eq,
      MaximumCall621Leaf148Chunk03From860.values_eq,
      MaximumCall621Leaf148Chunk04From860.values_eq,
      MaximumCall621Leaf148Chunk05From860.values_eq,
      MaximumCall621Leaf148Chunk06From860.values_eq,
      MaximumCall621Leaf148Chunk07From860.values_eq,
      MaximumCall621Leaf148Chunk08From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
