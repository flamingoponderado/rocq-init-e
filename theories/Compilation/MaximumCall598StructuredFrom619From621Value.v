From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall598StructuredFrom619From621Context MaximumCall598StructuredFrom619From621Chunk00 MaximumCall598StructuredFrom619From621Chunk01 MaximumCall598StructuredFrom619From621Chunk02 MaximumCall598StructuredFrom619From621Chunk03 MaximumCall598StructuredFrom619From621Chunk04 MaximumCall598StructuredFrom619From621Chunk05 MaximumCall598StructuredFrom619From621Chunk06 MaximumCall598StructuredFrom619From621Chunk07 MaximumCall598StructuredFrom619From621Chunk08 MaximumCall598StructuredFrom619From621Chunk09 MaximumCall598StructuredFrom619From621Chunk10 MaximumCall598StructuredFrom619From621Chunk11.

Definition values :=
  MaximumCall598StructuredFrom619From621Chunk00.values ++
  MaximumCall598StructuredFrom619From621Chunk01.values ++
  MaximumCall598StructuredFrom619From621Chunk02.values ++
  MaximumCall598StructuredFrom619From621Chunk03.values ++
  MaximumCall598StructuredFrom619From621Chunk04.values ++
  MaximumCall598StructuredFrom619From621Chunk05.values ++
  MaximumCall598StructuredFrom619From621Chunk06.values ++
  MaximumCall598StructuredFrom619From621Chunk07.values ++
  MaximumCall598StructuredFrom619From621Chunk08.values ++
  MaximumCall598StructuredFrom619From621Chunk09.values ++
  MaximumCall598StructuredFrom619From621Chunk10.values ++
  MaximumCall598StructuredFrom619From621Chunk11.values.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom619From621Context.depth MaximumCall598StructuredFrom619From621Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 12
    MaximumCall598StructuredFrom619From621Context.depth MaximumCall598StructuredFrom619From621Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall598StructuredFrom619From621Chunk00.values_eq,
      MaximumCall598StructuredFrom619From621Chunk01.values_eq,
      MaximumCall598StructuredFrom619From621Chunk02.values_eq,
      MaximumCall598StructuredFrom619From621Chunk03.values_eq,
      MaximumCall598StructuredFrom619From621Chunk04.values_eq,
      MaximumCall598StructuredFrom619From621Chunk05.values_eq,
      MaximumCall598StructuredFrom619From621Chunk06.values_eq,
      MaximumCall598StructuredFrom619From621Chunk07.values_eq,
      MaximumCall598StructuredFrom619From621Chunk08.values_eq,
      MaximumCall598StructuredFrom619From621Chunk09.values_eq,
      MaximumCall598StructuredFrom619From621Chunk10.values_eq,
      MaximumCall598StructuredFrom619From621Chunk11.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
