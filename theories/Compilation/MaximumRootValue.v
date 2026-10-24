From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumContext MaximumRootChunk00 MaximumRootChunk01 MaximumRootChunk02 MaximumRootChunk03 MaximumRootChunk04 MaximumRootChunk05 MaximumRootChunk06 MaximumRootChunk07 MaximumRootChunk08 MaximumRootChunk09 MaximumRootChunk10 MaximumRootChunk11 MaximumRootChunk12 MaximumRootChunk13 MaximumRootChunk14 MaximumRootChunk15 MaximumRootChunk16 MaximumRootChunk17 MaximumRootChunk18 MaximumRootChunk19 MaximumRootChunk20 MaximumRootChunk21 MaximumRootChunk22 MaximumRootChunk23 MaximumRootChunk24 MaximumRootChunk25 MaximumRootChunk26 MaximumRootChunk27 MaximumRootChunk28 MaximumRootChunk29 MaximumRootChunk30 MaximumRootChunk31 MaximumRootChunk32 MaximumRootChunk33 MaximumRootChunk34 MaximumRootChunk35 MaximumRootChunk36 MaximumRootChunk37 MaximumRootChunk38 MaximumRootChunk39 MaximumRootChunk40 MaximumRootChunk41 MaximumRootChunk42.

Definition values :=
  MaximumRootChunk00.values ++
  MaximumRootChunk01.values ++
  MaximumRootChunk02.values ++
  MaximumRootChunk03.values ++
  MaximumRootChunk04.values ++
  MaximumRootChunk05.values ++
  MaximumRootChunk06.values ++
  MaximumRootChunk07.values ++
  MaximumRootChunk08.values ++
  MaximumRootChunk09.values ++
  MaximumRootChunk10.values ++
  MaximumRootChunk11.values ++
  MaximumRootChunk12.values ++
  MaximumRootChunk13.values ++
  MaximumRootChunk14.values ++
  MaximumRootChunk15.values ++
  MaximumRootChunk16.values ++
  MaximumRootChunk17.values ++
  MaximumRootChunk18.values ++
  MaximumRootChunk19.values ++
  MaximumRootChunk20.values ++
  MaximumRootChunk21.values ++
  MaximumRootChunk22.values ++
  MaximumRootChunk23.values ++
  MaximumRootChunk24.values ++
  MaximumRootChunk25.values ++
  MaximumRootChunk26.values ++
  MaximumRootChunk27.values ++
  MaximumRootChunk28.values ++
  MaximumRootChunk29.values ++
  MaximumRootChunk30.values ++
  MaximumRootChunk31.values ++
  MaximumRootChunk32.values ++
  MaximumRootChunk33.values ++
  MaximumRootChunk34.values ++
  MaximumRootChunk35.values ++
  MaximumRootChunk36.values ++
  MaximumRootChunk37.values ++
  MaximumRootChunk38.values ++
  MaximumRootChunk39.values ++
  MaximumRootChunk40.values ++
  MaximumRootChunk41.values ++
  MaximumRootChunk42.values.

Lemma values_eq :
  List.map MaximumContext.depth MaximumContext.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 43
    MaximumContext.depth MaximumContext.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumRootChunk00.values_eq,
      MaximumRootChunk01.values_eq,
      MaximumRootChunk02.values_eq,
      MaximumRootChunk03.values_eq,
      MaximumRootChunk04.values_eq,
      MaximumRootChunk05.values_eq,
      MaximumRootChunk06.values_eq,
      MaximumRootChunk07.values_eq,
      MaximumRootChunk08.values_eq,
      MaximumRootChunk09.values_eq,
      MaximumRootChunk10.values_eq,
      MaximumRootChunk11.values_eq,
      MaximumRootChunk12.values_eq,
      MaximumRootChunk13.values_eq,
      MaximumRootChunk14.values_eq,
      MaximumRootChunk15.values_eq,
      MaximumRootChunk16.values_eq,
      MaximumRootChunk17.values_eq,
      MaximumRootChunk18.values_eq,
      MaximumRootChunk19.values_eq,
      MaximumRootChunk20.values_eq,
      MaximumRootChunk21.values_eq,
      MaximumRootChunk22.values_eq,
      MaximumRootChunk23.values_eq,
      MaximumRootChunk24.values_eq,
      MaximumRootChunk25.values_eq,
      MaximumRootChunk26.values_eq,
      MaximumRootChunk27.values_eq,
      MaximumRootChunk28.values_eq,
      MaximumRootChunk29.values_eq,
      MaximumRootChunk30.values_eq,
      MaximumRootChunk31.values_eq,
      MaximumRootChunk32.values_eq,
      MaximumRootChunk33.values_eq,
      MaximumRootChunk34.values_eq,
      MaximumRootChunk35.values_eq,
      MaximumRootChunk36.values_eq,
      MaximumRootChunk37.values_eq,
      MaximumRootChunk38.values_eq,
      MaximumRootChunk39.values_eq,
      MaximumRootChunk40.values_eq,
      MaximumRootChunk41.values_eq,
      MaximumRootChunk42.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
