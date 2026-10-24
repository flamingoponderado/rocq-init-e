From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall603Via619From621ContextFrom860From861 MaximumCall603Via619From621Chunk00From860From861 MaximumCall603Via619From621Chunk01From860From861 MaximumCall603Via619From621Chunk02From860From861 MaximumCall603Via619From621Chunk03From860From861 MaximumCall603Via619From621Chunk04From860From861 MaximumCall603Via619From621Chunk05From860From861 MaximumCall603Via619From621Chunk06From860From861 MaximumCall603Via619From621Chunk07From860From861 MaximumCall603Via619From621Chunk08From860From861.

Definition values :=
  MaximumCall603Via619From621Chunk00From860From861.values ++
  MaximumCall603Via619From621Chunk01From860From861.values ++
  MaximumCall603Via619From621Chunk02From860From861.values ++
  MaximumCall603Via619From621Chunk03From860From861.values ++
  MaximumCall603Via619From621Chunk04From860From861.values ++
  MaximumCall603Via619From621Chunk05From860From861.values ++
  MaximumCall603Via619From621Chunk06From860From861.values ++
  MaximumCall603Via619From621Chunk07From860From861.values ++
  MaximumCall603Via619From621Chunk08From860From861.values.

Lemma values_eq :
  List.map MaximumCall603Via619From621ContextFrom860From861.depth MaximumCall603Via619From621ContextFrom860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 9
    MaximumCall603Via619From621ContextFrom860From861.depth MaximumCall603Via619From621ContextFrom860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall603Via619From621Chunk00From860From861.values_eq,
      MaximumCall603Via619From621Chunk01From860From861.values_eq,
      MaximumCall603Via619From621Chunk02From860From861.values_eq,
      MaximumCall603Via619From621Chunk03From860From861.values_eq,
      MaximumCall603Via619From621Chunk04From860From861.values_eq,
      MaximumCall603Via619From621Chunk05From860From861.values_eq,
      MaximumCall603Via619From621Chunk06From860From861.values_eq,
      MaximumCall603Via619From621Chunk07From860From861.values_eq,
      MaximumCall603Via619From621Chunk08From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
