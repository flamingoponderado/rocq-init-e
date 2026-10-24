From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall603Via619From623ContextFrom860 MaximumCall603Via619From623Chunk00From860 MaximumCall603Via619From623Chunk01From860 MaximumCall603Via619From623Chunk02From860 MaximumCall603Via619From623Chunk03From860 MaximumCall603Via619From623Chunk04From860 MaximumCall603Via619From623Chunk05From860 MaximumCall603Via619From623Chunk06From860 MaximumCall603Via619From623Chunk07From860 MaximumCall603Via619From623Chunk08From860.

Definition values :=
  MaximumCall603Via619From623Chunk00From860.values ++
  MaximumCall603Via619From623Chunk01From860.values ++
  MaximumCall603Via619From623Chunk02From860.values ++
  MaximumCall603Via619From623Chunk03From860.values ++
  MaximumCall603Via619From623Chunk04From860.values ++
  MaximumCall603Via619From623Chunk05From860.values ++
  MaximumCall603Via619From623Chunk06From860.values ++
  MaximumCall603Via619From623Chunk07From860.values ++
  MaximumCall603Via619From623Chunk08From860.values.

Lemma values_eq :
  List.map MaximumCall603Via619From623ContextFrom860.depth MaximumCall603Via619From623ContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 9
    MaximumCall603Via619From623ContextFrom860.depth MaximumCall603Via619From623ContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall603Via619From623Chunk00From860.values_eq,
      MaximumCall603Via619From623Chunk01From860.values_eq,
      MaximumCall603Via619From623Chunk02From860.values_eq,
      MaximumCall603Via619From623Chunk03From860.values_eq,
      MaximumCall603Via619From623Chunk04From860.values_eq,
      MaximumCall603Via619From623Chunk05From860.values_eq,
      MaximumCall603Via619From623Chunk06From860.values_eq,
      MaximumCall603Via619From623Chunk07From860.values_eq,
      MaximumCall603Via619From623Chunk08From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
