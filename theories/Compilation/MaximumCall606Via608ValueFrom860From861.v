From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall606Via608ContextFrom860From861 MaximumCall606Via608Chunk00From860From861 MaximumCall606Via608Chunk01From860From861 MaximumCall606Via608Chunk02From860From861 MaximumCall606Via608Chunk03From860From861 MaximumCall606Via608Chunk04From860From861 MaximumCall606Via608Chunk05From860From861.

Definition values :=
  MaximumCall606Via608Chunk00From860From861.values ++
  MaximumCall606Via608Chunk01From860From861.values ++
  MaximumCall606Via608Chunk02From860From861.values ++
  MaximumCall606Via608Chunk03From860From861.values ++
  MaximumCall606Via608Chunk04From860From861.values ++
  MaximumCall606Via608Chunk05From860From861.values.

Lemma values_eq :
  List.map MaximumCall606Via608ContextFrom860From861.depth MaximumCall606Via608ContextFrom860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 6
    MaximumCall606Via608ContextFrom860From861.depth MaximumCall606Via608ContextFrom860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall606Via608Chunk00From860From861.values_eq,
      MaximumCall606Via608Chunk01From860From861.values_eq,
      MaximumCall606Via608Chunk02From860From861.values_eq,
      MaximumCall606Via608Chunk03From860From861.values_eq,
      MaximumCall606Via608Chunk04From860From861.values_eq,
      MaximumCall606Via608Chunk05From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
