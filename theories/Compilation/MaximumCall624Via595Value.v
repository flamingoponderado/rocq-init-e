From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall624Via595Context MaximumCall624Via595Chunk00 MaximumCall624Via595Chunk01 MaximumCall624Via595Chunk02 MaximumCall624Via595Chunk03 MaximumCall624Via595Chunk04 MaximumCall624Via595Chunk05 MaximumCall624Via595Chunk06 MaximumCall624Via595Chunk07 MaximumCall624Via595Chunk08 MaximumCall624Via595Chunk09 MaximumCall624Via595Chunk10 MaximumCall624Via595Chunk11 MaximumCall624Via595Chunk12 MaximumCall624Via595Chunk13 MaximumCall624Via595Chunk14 MaximumCall624Via595Chunk15 MaximumCall624Via595Chunk16.

Definition values :=
  MaximumCall624Via595Chunk00.values ++
  MaximumCall624Via595Chunk01.values ++
  MaximumCall624Via595Chunk02.values ++
  MaximumCall624Via595Chunk03.values ++
  MaximumCall624Via595Chunk04.values ++
  MaximumCall624Via595Chunk05.values ++
  MaximumCall624Via595Chunk06.values ++
  MaximumCall624Via595Chunk07.values ++
  MaximumCall624Via595Chunk08.values ++
  MaximumCall624Via595Chunk09.values ++
  MaximumCall624Via595Chunk10.values ++
  MaximumCall624Via595Chunk11.values ++
  MaximumCall624Via595Chunk12.values ++
  MaximumCall624Via595Chunk13.values ++
  MaximumCall624Via595Chunk14.values ++
  MaximumCall624Via595Chunk15.values ++
  MaximumCall624Via595Chunk16.values.

Lemma values_eq :
  List.map MaximumCall624Via595Context.depth MaximumCall624Via595Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 17
    MaximumCall624Via595Context.depth MaximumCall624Via595Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall624Via595Chunk00.values_eq,
      MaximumCall624Via595Chunk01.values_eq,
      MaximumCall624Via595Chunk02.values_eq,
      MaximumCall624Via595Chunk03.values_eq,
      MaximumCall624Via595Chunk04.values_eq,
      MaximumCall624Via595Chunk05.values_eq,
      MaximumCall624Via595Chunk06.values_eq,
      MaximumCall624Via595Chunk07.values_eq,
      MaximumCall624Via595Chunk08.values_eq,
      MaximumCall624Via595Chunk09.values_eq,
      MaximumCall624Via595Chunk10.values_eq,
      MaximumCall624Via595Chunk11.values_eq,
      MaximumCall624Via595Chunk12.values_eq,
      MaximumCall624Via595Chunk13.values_eq,
      MaximumCall624Via595Chunk14.values_eq,
      MaximumCall624Via595Chunk15.values_eq,
      MaximumCall624Via595Chunk16.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
