From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall621Leaf148ContextFrom860From861 MaximumCall621Leaf148Chunk00From860From861 MaximumCall621Leaf148Chunk01From860From861 MaximumCall621Leaf148Chunk02From860From861 MaximumCall621Leaf148Chunk03From860From861 MaximumCall621Leaf148Chunk04From860From861 MaximumCall621Leaf148Chunk05From860From861 MaximumCall621Leaf148Chunk06From860From861 MaximumCall621Leaf148Chunk07From860From861 MaximumCall621Leaf148Chunk08From860From861.

Definition values :=
  MaximumCall621Leaf148Chunk00From860From861.values ++
  MaximumCall621Leaf148Chunk01From860From861.values ++
  MaximumCall621Leaf148Chunk02From860From861.values ++
  MaximumCall621Leaf148Chunk03From860From861.values ++
  MaximumCall621Leaf148Chunk04From860From861.values ++
  MaximumCall621Leaf148Chunk05From860From861.values ++
  MaximumCall621Leaf148Chunk06From860From861.values ++
  MaximumCall621Leaf148Chunk07From860From861.values ++
  MaximumCall621Leaf148Chunk08From860From861.values.

Lemma values_eq :
  List.map MaximumCall621Leaf148ContextFrom860From861.depth MaximumCall621Leaf148ContextFrom860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 9
    MaximumCall621Leaf148ContextFrom860From861.depth MaximumCall621Leaf148ContextFrom860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall621Leaf148Chunk00From860From861.values_eq,
      MaximumCall621Leaf148Chunk01From860From861.values_eq,
      MaximumCall621Leaf148Chunk02From860From861.values_eq,
      MaximumCall621Leaf148Chunk03From860From861.values_eq,
      MaximumCall621Leaf148Chunk04From860From861.values_eq,
      MaximumCall621Leaf148Chunk05From860From861.values_eq,
      MaximumCall621Leaf148Chunk06From860From861.values_eq,
      MaximumCall621Leaf148Chunk07From860From861.values_eq,
      MaximumCall621Leaf148Chunk08From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
