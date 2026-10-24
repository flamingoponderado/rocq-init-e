From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall867StructuredContext MaximumCall867StructuredChunk00 MaximumCall867StructuredChunk01 MaximumCall867StructuredChunk02 MaximumCall867StructuredChunk03 MaximumCall867StructuredChunk04 MaximumCall867StructuredChunk05 MaximumCall867StructuredChunk06 MaximumCall867StructuredChunk07 MaximumCall867StructuredChunk08 MaximumCall867StructuredChunk09 MaximumCall867StructuredChunk10 MaximumCall867StructuredChunk11 MaximumCall867StructuredChunk12 MaximumCall867StructuredChunk13 MaximumCall867StructuredChunk14 MaximumCall867StructuredChunk15 MaximumCall867StructuredChunk16 MaximumCall867StructuredChunk17 MaximumCall867StructuredChunk18 MaximumCall867StructuredChunk19 MaximumCall867StructuredChunk20 MaximumCall867StructuredChunk21 MaximumCall867StructuredChunk22 MaximumCall867StructuredChunk23 MaximumCall867StructuredChunk24 MaximumCall867StructuredChunk25 MaximumCall867StructuredChunk26 MaximumCall867StructuredChunk27 MaximumCall867StructuredChunk28 MaximumCall867StructuredChunk29.

Definition values :=
  MaximumCall867StructuredChunk00.values ++
  MaximumCall867StructuredChunk01.values ++
  MaximumCall867StructuredChunk02.values ++
  MaximumCall867StructuredChunk03.values ++
  MaximumCall867StructuredChunk04.values ++
  MaximumCall867StructuredChunk05.values ++
  MaximumCall867StructuredChunk06.values ++
  MaximumCall867StructuredChunk07.values ++
  MaximumCall867StructuredChunk08.values ++
  MaximumCall867StructuredChunk09.values ++
  MaximumCall867StructuredChunk10.values ++
  MaximumCall867StructuredChunk11.values ++
  MaximumCall867StructuredChunk12.values ++
  MaximumCall867StructuredChunk13.values ++
  MaximumCall867StructuredChunk14.values ++
  MaximumCall867StructuredChunk15.values ++
  MaximumCall867StructuredChunk16.values ++
  MaximumCall867StructuredChunk17.values ++
  MaximumCall867StructuredChunk18.values ++
  MaximumCall867StructuredChunk19.values ++
  MaximumCall867StructuredChunk20.values ++
  MaximumCall867StructuredChunk21.values ++
  MaximumCall867StructuredChunk22.values ++
  MaximumCall867StructuredChunk23.values ++
  MaximumCall867StructuredChunk24.values ++
  MaximumCall867StructuredChunk25.values ++
  MaximumCall867StructuredChunk26.values ++
  MaximumCall867StructuredChunk27.values ++
  MaximumCall867StructuredChunk28.values ++
  MaximumCall867StructuredChunk29.values.

Lemma values_eq :
  List.map MaximumCall867StructuredContext.depth MaximumCall867StructuredContext.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 30
    MaximumCall867StructuredContext.depth MaximumCall867StructuredContext.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall867StructuredChunk00.values_eq,
      MaximumCall867StructuredChunk01.values_eq,
      MaximumCall867StructuredChunk02.values_eq,
      MaximumCall867StructuredChunk03.values_eq,
      MaximumCall867StructuredChunk04.values_eq,
      MaximumCall867StructuredChunk05.values_eq,
      MaximumCall867StructuredChunk06.values_eq,
      MaximumCall867StructuredChunk07.values_eq,
      MaximumCall867StructuredChunk08.values_eq,
      MaximumCall867StructuredChunk09.values_eq,
      MaximumCall867StructuredChunk10.values_eq,
      MaximumCall867StructuredChunk11.values_eq,
      MaximumCall867StructuredChunk12.values_eq,
      MaximumCall867StructuredChunk13.values_eq,
      MaximumCall867StructuredChunk14.values_eq,
      MaximumCall867StructuredChunk15.values_eq,
      MaximumCall867StructuredChunk16.values_eq,
      MaximumCall867StructuredChunk17.values_eq,
      MaximumCall867StructuredChunk18.values_eq,
      MaximumCall867StructuredChunk19.values_eq,
      MaximumCall867StructuredChunk20.values_eq,
      MaximumCall867StructuredChunk21.values_eq,
      MaximumCall867StructuredChunk22.values_eq,
      MaximumCall867StructuredChunk23.values_eq,
      MaximumCall867StructuredChunk24.values_eq,
      MaximumCall867StructuredChunk25.values_eq,
      MaximumCall867StructuredChunk26.values_eq,
      MaximumCall867StructuredChunk27.values_eq,
      MaximumCall867StructuredChunk28.values_eq,
      MaximumCall867StructuredChunk29.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
