From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall625Via860ContextFrom861 MaximumCall625Via860Chunk00From861 MaximumCall625Via860Chunk01From861 MaximumCall625Via860Chunk02From861 MaximumCall625Via860Chunk03From861 MaximumCall625Via860Chunk04From861 MaximumCall625Via860Chunk05From861 MaximumCall625Via860Chunk06From861 MaximumCall625Via860Chunk07From861 MaximumCall625Via860Chunk08From861 MaximumCall625Via860Chunk09From861.

Definition values :=
  MaximumCall625Via860Chunk00From861.values ++
  MaximumCall625Via860Chunk01From861.values ++
  MaximumCall625Via860Chunk02From861.values ++
  MaximumCall625Via860Chunk03From861.values ++
  MaximumCall625Via860Chunk04From861.values ++
  MaximumCall625Via860Chunk05From861.values ++
  MaximumCall625Via860Chunk06From861.values ++
  MaximumCall625Via860Chunk07From861.values ++
  MaximumCall625Via860Chunk08From861.values ++
  MaximumCall625Via860Chunk09From861.values.

Lemma values_eq :
  List.map MaximumCall625Via860ContextFrom861.depth MaximumCall625Via860ContextFrom861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 10
    MaximumCall625Via860ContextFrom861.depth MaximumCall625Via860ContextFrom861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall625Via860Chunk00From861.values_eq,
      MaximumCall625Via860Chunk01From861.values_eq,
      MaximumCall625Via860Chunk02From861.values_eq,
      MaximumCall625Via860Chunk03From861.values_eq,
      MaximumCall625Via860Chunk04From861.values_eq,
      MaximumCall625Via860Chunk05From861.values_eq,
      MaximumCall625Via860Chunk06From861.values_eq,
      MaximumCall625Via860Chunk07From861.values_eq,
      MaximumCall625Via860Chunk08From861.values_eq,
      MaximumCall625Via860Chunk09From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
