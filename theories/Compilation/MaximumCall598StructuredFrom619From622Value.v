From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall598StructuredFrom619From622Context MaximumCall598StructuredFrom619From622Chunk00 MaximumCall598StructuredFrom619From622Chunk01 MaximumCall598StructuredFrom619From622Chunk02 MaximumCall598StructuredFrom619From622Chunk03 MaximumCall598StructuredFrom619From622Chunk04 MaximumCall598StructuredFrom619From622Chunk05 MaximumCall598StructuredFrom619From622Chunk06 MaximumCall598StructuredFrom619From622Chunk07 MaximumCall598StructuredFrom619From622Chunk08 MaximumCall598StructuredFrom619From622Chunk09 MaximumCall598StructuredFrom619From622Chunk10 MaximumCall598StructuredFrom619From622Chunk11.

Definition values :=
  MaximumCall598StructuredFrom619From622Chunk00.values ++
  MaximumCall598StructuredFrom619From622Chunk01.values ++
  MaximumCall598StructuredFrom619From622Chunk02.values ++
  MaximumCall598StructuredFrom619From622Chunk03.values ++
  MaximumCall598StructuredFrom619From622Chunk04.values ++
  MaximumCall598StructuredFrom619From622Chunk05.values ++
  MaximumCall598StructuredFrom619From622Chunk06.values ++
  MaximumCall598StructuredFrom619From622Chunk07.values ++
  MaximumCall598StructuredFrom619From622Chunk08.values ++
  MaximumCall598StructuredFrom619From622Chunk09.values ++
  MaximumCall598StructuredFrom619From622Chunk10.values ++
  MaximumCall598StructuredFrom619From622Chunk11.values.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom619From622Context.depth MaximumCall598StructuredFrom619From622Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 12
    MaximumCall598StructuredFrom619From622Context.depth MaximumCall598StructuredFrom619From622Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall598StructuredFrom619From622Chunk00.values_eq,
      MaximumCall598StructuredFrom619From622Chunk01.values_eq,
      MaximumCall598StructuredFrom619From622Chunk02.values_eq,
      MaximumCall598StructuredFrom619From622Chunk03.values_eq,
      MaximumCall598StructuredFrom619From622Chunk04.values_eq,
      MaximumCall598StructuredFrom619From622Chunk05.values_eq,
      MaximumCall598StructuredFrom619From622Chunk06.values_eq,
      MaximumCall598StructuredFrom619From622Chunk07.values_eq,
      MaximumCall598StructuredFrom619From622Chunk08.values_eq,
      MaximumCall598StructuredFrom619From622Chunk09.values_eq,
      MaximumCall598StructuredFrom619From622Chunk10.values_eq,
      MaximumCall598StructuredFrom619From622Chunk11.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
