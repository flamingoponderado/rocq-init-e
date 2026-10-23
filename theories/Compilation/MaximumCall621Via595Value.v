From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall621Via595Context MaximumCall621Via595Chunk00 MaximumCall621Via595Chunk01 MaximumCall621Via595Chunk02 MaximumCall621Via595Chunk03 MaximumCall621Via595Chunk04 MaximumCall621Via595Chunk05 MaximumCall621Via595Chunk06 MaximumCall621Via595Chunk07 MaximumCall621Via595Chunk08 MaximumCall621Via595Chunk09 MaximumCall621Via595Chunk10 MaximumCall621Via595Chunk11 MaximumCall621Via595Chunk12 MaximumCall621Via595Chunk13 MaximumCall621Via595Chunk14 MaximumCall621Via595Chunk15 MaximumCall621Via595Chunk16 MaximumCall621Via595Chunk17 MaximumCall621Via595Chunk18 MaximumCall621Via595Chunk19.

Definition values :=
  MaximumCall621Via595Chunk00.values ++
  MaximumCall621Via595Chunk01.values ++
  MaximumCall621Via595Chunk02.values ++
  MaximumCall621Via595Chunk03.values ++
  MaximumCall621Via595Chunk04.values ++
  MaximumCall621Via595Chunk05.values ++
  MaximumCall621Via595Chunk06.values ++
  MaximumCall621Via595Chunk07.values ++
  MaximumCall621Via595Chunk08.values ++
  MaximumCall621Via595Chunk09.values ++
  MaximumCall621Via595Chunk10.values ++
  MaximumCall621Via595Chunk11.values ++
  MaximumCall621Via595Chunk12.values ++
  MaximumCall621Via595Chunk13.values ++
  MaximumCall621Via595Chunk14.values ++
  MaximumCall621Via595Chunk15.values ++
  MaximumCall621Via595Chunk16.values ++
  MaximumCall621Via595Chunk17.values ++
  MaximumCall621Via595Chunk18.values ++
  MaximumCall621Via595Chunk19.values.

Lemma values_eq :
  List.map MaximumCall621Via595Context.depth MaximumCall621Via595Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 20
    MaximumCall621Via595Context.depth MaximumCall621Via595Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall621Via595Chunk00.values_eq,
      MaximumCall621Via595Chunk01.values_eq,
      MaximumCall621Via595Chunk02.values_eq,
      MaximumCall621Via595Chunk03.values_eq,
      MaximumCall621Via595Chunk04.values_eq,
      MaximumCall621Via595Chunk05.values_eq,
      MaximumCall621Via595Chunk06.values_eq,
      MaximumCall621Via595Chunk07.values_eq,
      MaximumCall621Via595Chunk08.values_eq,
      MaximumCall621Via595Chunk09.values_eq,
      MaximumCall621Via595Chunk10.values_eq,
      MaximumCall621Via595Chunk11.values_eq,
      MaximumCall621Via595Chunk12.values_eq,
      MaximumCall621Via595Chunk13.values_eq,
      MaximumCall621Via595Chunk14.values_eq,
      MaximumCall621Via595Chunk15.values_eq,
      MaximumCall621Via595Chunk16.values_eq,
      MaximumCall621Via595Chunk17.values_eq,
      MaximumCall621Via595Chunk18.values_eq,
      MaximumCall621Via595Chunk19.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
