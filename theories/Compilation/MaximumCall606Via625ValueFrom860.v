From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall606Via625ContextFrom860 MaximumCall606Via625Chunk00From860 MaximumCall606Via625Chunk01From860 MaximumCall606Via625Chunk02From860 MaximumCall606Via625Chunk03From860 MaximumCall606Via625Chunk04From860 MaximumCall606Via625Chunk05From860.

Definition values :=
  MaximumCall606Via625Chunk00From860.values ++
  MaximumCall606Via625Chunk01From860.values ++
  MaximumCall606Via625Chunk02From860.values ++
  MaximumCall606Via625Chunk03From860.values ++
  MaximumCall606Via625Chunk04From860.values ++
  MaximumCall606Via625Chunk05From860.values.

Lemma values_eq :
  List.map MaximumCall606Via625ContextFrom860.depth MaximumCall606Via625ContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 6
    MaximumCall606Via625ContextFrom860.depth MaximumCall606Via625ContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall606Via625Chunk00From860.values_eq,
      MaximumCall606Via625Chunk01From860.values_eq,
      MaximumCall606Via625Chunk02From860.values_eq,
      MaximumCall606Via625Chunk03From860.values_eq,
      MaximumCall606Via625Chunk04From860.values_eq,
      MaximumCall606Via625Chunk05From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
