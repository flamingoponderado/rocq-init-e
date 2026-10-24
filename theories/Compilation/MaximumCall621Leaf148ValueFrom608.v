From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall621Leaf148ContextFrom608 MaximumCall621Leaf148Chunk00From608 MaximumCall621Leaf148Chunk01From608 MaximumCall621Leaf148Chunk02From608 MaximumCall621Leaf148Chunk03From608 MaximumCall621Leaf148Chunk04From608 MaximumCall621Leaf148Chunk05From608 MaximumCall621Leaf148Chunk06From608 MaximumCall621Leaf148Chunk07From608 MaximumCall621Leaf148Chunk08From608.

Definition values :=
  MaximumCall621Leaf148Chunk00From608.values ++
  MaximumCall621Leaf148Chunk01From608.values ++
  MaximumCall621Leaf148Chunk02From608.values ++
  MaximumCall621Leaf148Chunk03From608.values ++
  MaximumCall621Leaf148Chunk04From608.values ++
  MaximumCall621Leaf148Chunk05From608.values ++
  MaximumCall621Leaf148Chunk06From608.values ++
  MaximumCall621Leaf148Chunk07From608.values ++
  MaximumCall621Leaf148Chunk08From608.values.

Lemma values_eq :
  List.map MaximumCall621Leaf148ContextFrom608.depth MaximumCall621Leaf148ContextFrom608.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 9
    MaximumCall621Leaf148ContextFrom608.depth MaximumCall621Leaf148ContextFrom608.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall621Leaf148Chunk00From608.values_eq,
      MaximumCall621Leaf148Chunk01From608.values_eq,
      MaximumCall621Leaf148Chunk02From608.values_eq,
      MaximumCall621Leaf148Chunk03From608.values_eq,
      MaximumCall621Leaf148Chunk04From608.values_eq,
      MaximumCall621Leaf148Chunk05From608.values_eq,
      MaximumCall621Leaf148Chunk06From608.values_eq,
      MaximumCall621Leaf148Chunk07From608.values_eq,
      MaximumCall621Leaf148Chunk08From608.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
