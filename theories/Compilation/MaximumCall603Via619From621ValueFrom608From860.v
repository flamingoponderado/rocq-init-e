From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall603Via619From621ContextFrom608From860 MaximumCall603Via619From621Chunk00From608From860 MaximumCall603Via619From621Chunk01From608From860 MaximumCall603Via619From621Chunk02From608From860 MaximumCall603Via619From621Chunk03From608From860 MaximumCall603Via619From621Chunk04From608From860 MaximumCall603Via619From621Chunk05From608From860 MaximumCall603Via619From621Chunk06From608From860 MaximumCall603Via619From621Chunk07From608From860 MaximumCall603Via619From621Chunk08From608From860.

Definition values :=
  MaximumCall603Via619From621Chunk00From608From860.values ++
  MaximumCall603Via619From621Chunk01From608From860.values ++
  MaximumCall603Via619From621Chunk02From608From860.values ++
  MaximumCall603Via619From621Chunk03From608From860.values ++
  MaximumCall603Via619From621Chunk04From608From860.values ++
  MaximumCall603Via619From621Chunk05From608From860.values ++
  MaximumCall603Via619From621Chunk06From608From860.values ++
  MaximumCall603Via619From621Chunk07From608From860.values ++
  MaximumCall603Via619From621Chunk08From608From860.values.

Lemma values_eq :
  List.map MaximumCall603Via619From621ContextFrom608From860.depth MaximumCall603Via619From621ContextFrom608From860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 9
    MaximumCall603Via619From621ContextFrom608From860.depth MaximumCall603Via619From621ContextFrom608From860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall603Via619From621Chunk00From608From860.values_eq,
      MaximumCall603Via619From621Chunk01From608From860.values_eq,
      MaximumCall603Via619From621Chunk02From608From860.values_eq,
      MaximumCall603Via619From621Chunk03From608From860.values_eq,
      MaximumCall603Via619From621Chunk04From608From860.values_eq,
      MaximumCall603Via619From621Chunk05From608From860.values_eq,
      MaximumCall603Via619From621Chunk06From608From860.values_eq,
      MaximumCall603Via619From621Chunk07From608From860.values_eq,
      MaximumCall603Via619From621Chunk08From608From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
