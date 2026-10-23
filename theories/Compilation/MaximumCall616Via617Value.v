From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall616Via617Context MaximumCall616Via617Chunk00 MaximumCall616Via617Chunk01 MaximumCall616Via617Chunk02 MaximumCall616Via617Chunk03 MaximumCall616Via617Chunk04 MaximumCall616Via617Chunk05 MaximumCall616Via617Chunk06 MaximumCall616Via617Chunk07 MaximumCall616Via617Chunk08 MaximumCall616Via617Chunk09 MaximumCall616Via617Chunk10 MaximumCall616Via617Chunk11 MaximumCall616Via617Chunk12 MaximumCall616Via617Chunk13 MaximumCall616Via617Chunk14 MaximumCall616Via617Chunk15 MaximumCall616Via617Chunk16.

Definition values :=
  MaximumCall616Via617Chunk00.values ++
  MaximumCall616Via617Chunk01.values ++
  MaximumCall616Via617Chunk02.values ++
  MaximumCall616Via617Chunk03.values ++
  MaximumCall616Via617Chunk04.values ++
  MaximumCall616Via617Chunk05.values ++
  MaximumCall616Via617Chunk06.values ++
  MaximumCall616Via617Chunk07.values ++
  MaximumCall616Via617Chunk08.values ++
  MaximumCall616Via617Chunk09.values ++
  MaximumCall616Via617Chunk10.values ++
  MaximumCall616Via617Chunk11.values ++
  MaximumCall616Via617Chunk12.values ++
  MaximumCall616Via617Chunk13.values ++
  MaximumCall616Via617Chunk14.values ++
  MaximumCall616Via617Chunk15.values ++
  MaximumCall616Via617Chunk16.values.

Lemma values_eq :
  List.map MaximumCall616Via617Context.depth MaximumCall616Via617Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 17
    MaximumCall616Via617Context.depth MaximumCall616Via617Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall616Via617Chunk00.values_eq,
      MaximumCall616Via617Chunk01.values_eq,
      MaximumCall616Via617Chunk02.values_eq,
      MaximumCall616Via617Chunk03.values_eq,
      MaximumCall616Via617Chunk04.values_eq,
      MaximumCall616Via617Chunk05.values_eq,
      MaximumCall616Via617Chunk06.values_eq,
      MaximumCall616Via617Chunk07.values_eq,
      MaximumCall616Via617Chunk08.values_eq,
      MaximumCall616Via617Chunk09.values_eq,
      MaximumCall616Via617Chunk10.values_eq,
      MaximumCall616Via617Chunk11.values_eq,
      MaximumCall616Via617Chunk12.values_eq,
      MaximumCall616Via617Chunk13.values_eq,
      MaximumCall616Via617Chunk14.values_eq,
      MaximumCall616Via617Chunk15.values_eq,
      MaximumCall616Via617Chunk16.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
