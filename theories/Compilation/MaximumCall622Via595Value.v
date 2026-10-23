From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall622Via595Context MaximumCall622Via595Chunk00 MaximumCall622Via595Chunk01 MaximumCall622Via595Chunk02 MaximumCall622Via595Chunk03 MaximumCall622Via595Chunk04 MaximumCall622Via595Chunk05 MaximumCall622Via595Chunk06 MaximumCall622Via595Chunk07 MaximumCall622Via595Chunk08 MaximumCall622Via595Chunk09 MaximumCall622Via595Chunk10 MaximumCall622Via595Chunk11 MaximumCall622Via595Chunk12 MaximumCall622Via595Chunk13 MaximumCall622Via595Chunk14 MaximumCall622Via595Chunk15 MaximumCall622Via595Chunk16 MaximumCall622Via595Chunk17.

Definition values :=
  MaximumCall622Via595Chunk00.values ++
  MaximumCall622Via595Chunk01.values ++
  MaximumCall622Via595Chunk02.values ++
  MaximumCall622Via595Chunk03.values ++
  MaximumCall622Via595Chunk04.values ++
  MaximumCall622Via595Chunk05.values ++
  MaximumCall622Via595Chunk06.values ++
  MaximumCall622Via595Chunk07.values ++
  MaximumCall622Via595Chunk08.values ++
  MaximumCall622Via595Chunk09.values ++
  MaximumCall622Via595Chunk10.values ++
  MaximumCall622Via595Chunk11.values ++
  MaximumCall622Via595Chunk12.values ++
  MaximumCall622Via595Chunk13.values ++
  MaximumCall622Via595Chunk14.values ++
  MaximumCall622Via595Chunk15.values ++
  MaximumCall622Via595Chunk16.values ++
  MaximumCall622Via595Chunk17.values.

Lemma values_eq :
  List.map MaximumCall622Via595Context.depth MaximumCall622Via595Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 18
    MaximumCall622Via595Context.depth MaximumCall622Via595Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall622Via595Chunk00.values_eq,
      MaximumCall622Via595Chunk01.values_eq,
      MaximumCall622Via595Chunk02.values_eq,
      MaximumCall622Via595Chunk03.values_eq,
      MaximumCall622Via595Chunk04.values_eq,
      MaximumCall622Via595Chunk05.values_eq,
      MaximumCall622Via595Chunk06.values_eq,
      MaximumCall622Via595Chunk07.values_eq,
      MaximumCall622Via595Chunk08.values_eq,
      MaximumCall622Via595Chunk09.values_eq,
      MaximumCall622Via595Chunk10.values_eq,
      MaximumCall622Via595Chunk11.values_eq,
      MaximumCall622Via595Chunk12.values_eq,
      MaximumCall622Via595Chunk13.values_eq,
      MaximumCall622Via595Chunk14.values_eq,
      MaximumCall622Via595Chunk15.values_eq,
      MaximumCall622Via595Chunk16.values_eq,
      MaximumCall622Via595Chunk17.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
