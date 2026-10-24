From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall865StructuredContext MaximumCall865StructuredChunk00 MaximumCall865StructuredChunk01 MaximumCall865StructuredChunk02 MaximumCall865StructuredChunk03 MaximumCall865StructuredChunk04 MaximumCall865StructuredChunk05 MaximumCall865StructuredChunk06 MaximumCall865StructuredChunk07 MaximumCall865StructuredChunk08 MaximumCall865StructuredChunk09 MaximumCall865StructuredChunk10 MaximumCall865StructuredChunk11 MaximumCall865StructuredChunk12.

Definition values :=
  MaximumCall865StructuredChunk00.values ++
  MaximumCall865StructuredChunk01.values ++
  MaximumCall865StructuredChunk02.values ++
  MaximumCall865StructuredChunk03.values ++
  MaximumCall865StructuredChunk04.values ++
  MaximumCall865StructuredChunk05.values ++
  MaximumCall865StructuredChunk06.values ++
  MaximumCall865StructuredChunk07.values ++
  MaximumCall865StructuredChunk08.values ++
  MaximumCall865StructuredChunk09.values ++
  MaximumCall865StructuredChunk10.values ++
  MaximumCall865StructuredChunk11.values ++
  MaximumCall865StructuredChunk12.values.

Lemma values_eq :
  List.map MaximumCall865StructuredContext.depth MaximumCall865StructuredContext.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 13
    MaximumCall865StructuredContext.depth MaximumCall865StructuredContext.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall865StructuredChunk00.values_eq,
      MaximumCall865StructuredChunk01.values_eq,
      MaximumCall865StructuredChunk02.values_eq,
      MaximumCall865StructuredChunk03.values_eq,
      MaximumCall865StructuredChunk04.values_eq,
      MaximumCall865StructuredChunk05.values_eq,
      MaximumCall865StructuredChunk06.values_eq,
      MaximumCall865StructuredChunk07.values_eq,
      MaximumCall865StructuredChunk08.values_eq,
      MaximumCall865StructuredChunk09.values_eq,
      MaximumCall865StructuredChunk10.values_eq,
      MaximumCall865StructuredChunk11.values_eq,
      MaximumCall865StructuredChunk12.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
