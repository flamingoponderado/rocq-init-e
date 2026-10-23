From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall623Via595Context MaximumCall623Via595Chunk00 MaximumCall623Via595Chunk01 MaximumCall623Via595Chunk02 MaximumCall623Via595Chunk03 MaximumCall623Via595Chunk04 MaximumCall623Via595Chunk05 MaximumCall623Via595Chunk06 MaximumCall623Via595Chunk07 MaximumCall623Via595Chunk08 MaximumCall623Via595Chunk09 MaximumCall623Via595Chunk10 MaximumCall623Via595Chunk11 MaximumCall623Via595Chunk12 MaximumCall623Via595Chunk13 MaximumCall623Via595Chunk14 MaximumCall623Via595Chunk15 MaximumCall623Via595Chunk16 MaximumCall623Via595Chunk17.

Definition values :=
  MaximumCall623Via595Chunk00.values ++
  MaximumCall623Via595Chunk01.values ++
  MaximumCall623Via595Chunk02.values ++
  MaximumCall623Via595Chunk03.values ++
  MaximumCall623Via595Chunk04.values ++
  MaximumCall623Via595Chunk05.values ++
  MaximumCall623Via595Chunk06.values ++
  MaximumCall623Via595Chunk07.values ++
  MaximumCall623Via595Chunk08.values ++
  MaximumCall623Via595Chunk09.values ++
  MaximumCall623Via595Chunk10.values ++
  MaximumCall623Via595Chunk11.values ++
  MaximumCall623Via595Chunk12.values ++
  MaximumCall623Via595Chunk13.values ++
  MaximumCall623Via595Chunk14.values ++
  MaximumCall623Via595Chunk15.values ++
  MaximumCall623Via595Chunk16.values ++
  MaximumCall623Via595Chunk17.values.

Lemma values_eq :
  List.map MaximumCall623Via595Context.depth MaximumCall623Via595Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 18
    MaximumCall623Via595Context.depth MaximumCall623Via595Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall623Via595Chunk00.values_eq,
      MaximumCall623Via595Chunk01.values_eq,
      MaximumCall623Via595Chunk02.values_eq,
      MaximumCall623Via595Chunk03.values_eq,
      MaximumCall623Via595Chunk04.values_eq,
      MaximumCall623Via595Chunk05.values_eq,
      MaximumCall623Via595Chunk06.values_eq,
      MaximumCall623Via595Chunk07.values_eq,
      MaximumCall623Via595Chunk08.values_eq,
      MaximumCall623Via595Chunk09.values_eq,
      MaximumCall623Via595Chunk10.values_eq,
      MaximumCall623Via595Chunk11.values_eq,
      MaximumCall623Via595Chunk12.values_eq,
      MaximumCall623Via595Chunk13.values_eq,
      MaximumCall623Via595Chunk14.values_eq,
      MaximumCall623Via595Chunk15.values_eq,
      MaximumCall623Via595Chunk16.values_eq,
      MaximumCall623Via595Chunk17.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
