From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall861StructuredContext MaximumCall861StructuredChunk00 MaximumCall861StructuredChunk01 MaximumCall861StructuredChunk02 MaximumCall861StructuredChunk03 MaximumCall861StructuredChunk04 MaximumCall861StructuredChunk05.

Definition values :=
  MaximumCall861StructuredChunk00.values ++
  MaximumCall861StructuredChunk01.values ++
  MaximumCall861StructuredChunk02.values ++
  MaximumCall861StructuredChunk03.values ++
  MaximumCall861StructuredChunk04.values ++
  MaximumCall861StructuredChunk05.values.

Lemma values_eq :
  List.map MaximumCall861StructuredContext.depth MaximumCall861StructuredContext.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 6
    MaximumCall861StructuredContext.depth MaximumCall861StructuredContext.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall861StructuredChunk00.values_eq,
      MaximumCall861StructuredChunk01.values_eq,
      MaximumCall861StructuredChunk02.values_eq,
      MaximumCall861StructuredChunk03.values_eq,
      MaximumCall861StructuredChunk04.values_eq,
      MaximumCall861StructuredChunk05.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
