From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall602Via606ContextFrom860 MaximumCall602Via606Chunk00From860 MaximumCall602Via606Chunk01From860.

Definition values :=
  MaximumCall602Via606Chunk00From860.values ++
  MaximumCall602Via606Chunk01From860.values.

Lemma values_eq :
  List.map MaximumCall602Via606ContextFrom860.depth MaximumCall602Via606ContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 2
    MaximumCall602Via606ContextFrom860.depth MaximumCall602Via606ContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall602Via606Chunk00From860.values_eq,
      MaximumCall602Via606Chunk01From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
