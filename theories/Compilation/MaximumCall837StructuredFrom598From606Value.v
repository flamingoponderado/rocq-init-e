From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall837StructuredFrom598From606Context MaximumCall837StructuredFrom598From606Chunk00 MaximumCall837StructuredFrom598From606Chunk01 MaximumCall837StructuredFrom598From606Chunk02 MaximumCall837StructuredFrom598From606Chunk03 MaximumCall837StructuredFrom598From606Chunk04 MaximumCall837StructuredFrom598From606Chunk05 MaximumCall837StructuredFrom598From606Chunk06 MaximumCall837StructuredFrom598From606Chunk07 MaximumCall837StructuredFrom598From606Chunk08 MaximumCall837StructuredFrom598From606Chunk09 MaximumCall837StructuredFrom598From606Chunk10 MaximumCall837StructuredFrom598From606Chunk11 MaximumCall837StructuredFrom598From606Chunk12 MaximumCall837StructuredFrom598From606Chunk13 MaximumCall837StructuredFrom598From606Chunk14 MaximumCall837StructuredFrom598From606Chunk15 MaximumCall837StructuredFrom598From606Chunk16 MaximumCall837StructuredFrom598From606Chunk17 MaximumCall837StructuredFrom598From606Chunk18 MaximumCall837StructuredFrom598From606Chunk19 MaximumCall837StructuredFrom598From606Chunk20 MaximumCall837StructuredFrom598From606Chunk21 MaximumCall837StructuredFrom598From606Chunk22 MaximumCall837StructuredFrom598From606Chunk23 MaximumCall837StructuredFrom598From606Chunk24 MaximumCall837StructuredFrom598From606Chunk25 MaximumCall837StructuredFrom598From606Chunk26 MaximumCall837StructuredFrom598From606Chunk27.

Definition values :=
  MaximumCall837StructuredFrom598From606Chunk00.values ++
  MaximumCall837StructuredFrom598From606Chunk01.values ++
  MaximumCall837StructuredFrom598From606Chunk02.values ++
  MaximumCall837StructuredFrom598From606Chunk03.values ++
  MaximumCall837StructuredFrom598From606Chunk04.values ++
  MaximumCall837StructuredFrom598From606Chunk05.values ++
  MaximumCall837StructuredFrom598From606Chunk06.values ++
  MaximumCall837StructuredFrom598From606Chunk07.values ++
  MaximumCall837StructuredFrom598From606Chunk08.values ++
  MaximumCall837StructuredFrom598From606Chunk09.values ++
  MaximumCall837StructuredFrom598From606Chunk10.values ++
  MaximumCall837StructuredFrom598From606Chunk11.values ++
  MaximumCall837StructuredFrom598From606Chunk12.values ++
  MaximumCall837StructuredFrom598From606Chunk13.values ++
  MaximumCall837StructuredFrom598From606Chunk14.values ++
  MaximumCall837StructuredFrom598From606Chunk15.values ++
  MaximumCall837StructuredFrom598From606Chunk16.values ++
  MaximumCall837StructuredFrom598From606Chunk17.values ++
  MaximumCall837StructuredFrom598From606Chunk18.values ++
  MaximumCall837StructuredFrom598From606Chunk19.values ++
  MaximumCall837StructuredFrom598From606Chunk20.values ++
  MaximumCall837StructuredFrom598From606Chunk21.values ++
  MaximumCall837StructuredFrom598From606Chunk22.values ++
  MaximumCall837StructuredFrom598From606Chunk23.values ++
  MaximumCall837StructuredFrom598From606Chunk24.values ++
  MaximumCall837StructuredFrom598From606Chunk25.values ++
  MaximumCall837StructuredFrom598From606Chunk26.values ++
  MaximumCall837StructuredFrom598From606Chunk27.values.

Lemma values_eq :
  List.map MaximumCall837StructuredFrom598From606Context.depth MaximumCall837StructuredFrom598From606Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 28
    MaximumCall837StructuredFrom598From606Context.depth MaximumCall837StructuredFrom598From606Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall837StructuredFrom598From606Chunk00.values_eq,
      MaximumCall837StructuredFrom598From606Chunk01.values_eq,
      MaximumCall837StructuredFrom598From606Chunk02.values_eq,
      MaximumCall837StructuredFrom598From606Chunk03.values_eq,
      MaximumCall837StructuredFrom598From606Chunk04.values_eq,
      MaximumCall837StructuredFrom598From606Chunk05.values_eq,
      MaximumCall837StructuredFrom598From606Chunk06.values_eq,
      MaximumCall837StructuredFrom598From606Chunk07.values_eq,
      MaximumCall837StructuredFrom598From606Chunk08.values_eq,
      MaximumCall837StructuredFrom598From606Chunk09.values_eq,
      MaximumCall837StructuredFrom598From606Chunk10.values_eq,
      MaximumCall837StructuredFrom598From606Chunk11.values_eq,
      MaximumCall837StructuredFrom598From606Chunk12.values_eq,
      MaximumCall837StructuredFrom598From606Chunk13.values_eq,
      MaximumCall837StructuredFrom598From606Chunk14.values_eq,
      MaximumCall837StructuredFrom598From606Chunk15.values_eq,
      MaximumCall837StructuredFrom598From606Chunk16.values_eq,
      MaximumCall837StructuredFrom598From606Chunk17.values_eq,
      MaximumCall837StructuredFrom598From606Chunk18.values_eq,
      MaximumCall837StructuredFrom598From606Chunk19.values_eq,
      MaximumCall837StructuredFrom598From606Chunk20.values_eq,
      MaximumCall837StructuredFrom598From606Chunk21.values_eq,
      MaximumCall837StructuredFrom598From606Chunk22.values_eq,
      MaximumCall837StructuredFrom598From606Chunk23.values_eq,
      MaximumCall837StructuredFrom598From606Chunk24.values_eq,
      MaximumCall837StructuredFrom598From606Chunk25.values_eq,
      MaximumCall837StructuredFrom598From606Chunk26.values_eq,
      MaximumCall837StructuredFrom598From606Chunk27.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
