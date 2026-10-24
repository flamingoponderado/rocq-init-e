From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall860Via861Context MaximumCall860Via861Chunk00 MaximumCall860Via861Chunk01 MaximumCall860Via861Chunk02 MaximumCall860Via861Chunk03 MaximumCall860Via861Chunk04 MaximumCall860Via861Chunk05 MaximumCall860Via861Chunk06 MaximumCall860Via861Chunk07 MaximumCall860Via861Chunk08 MaximumCall860Via861Chunk09 MaximumCall860Via861Chunk10 MaximumCall860Via861Chunk11 MaximumCall860Via861Chunk12 MaximumCall860Via861Chunk13 MaximumCall860Via861Chunk14 MaximumCall860Via861Chunk15 MaximumCall860Via861Chunk16 MaximumCall860Via861Chunk17.

Definition values :=
  MaximumCall860Via861Chunk00.values ++
  MaximumCall860Via861Chunk01.values ++
  MaximumCall860Via861Chunk02.values ++
  MaximumCall860Via861Chunk03.values ++
  MaximumCall860Via861Chunk04.values ++
  MaximumCall860Via861Chunk05.values ++
  MaximumCall860Via861Chunk06.values ++
  MaximumCall860Via861Chunk07.values ++
  MaximumCall860Via861Chunk08.values ++
  MaximumCall860Via861Chunk09.values ++
  MaximumCall860Via861Chunk10.values ++
  MaximumCall860Via861Chunk11.values ++
  MaximumCall860Via861Chunk12.values ++
  MaximumCall860Via861Chunk13.values ++
  MaximumCall860Via861Chunk14.values ++
  MaximumCall860Via861Chunk15.values ++
  MaximumCall860Via861Chunk16.values ++
  MaximumCall860Via861Chunk17.values.

Lemma values_eq :
  List.map MaximumCall860Via861Context.depth MaximumCall860Via861Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 18
    MaximumCall860Via861Context.depth MaximumCall860Via861Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall860Via861Chunk00.values_eq,
      MaximumCall860Via861Chunk01.values_eq,
      MaximumCall860Via861Chunk02.values_eq,
      MaximumCall860Via861Chunk03.values_eq,
      MaximumCall860Via861Chunk04.values_eq,
      MaximumCall860Via861Chunk05.values_eq,
      MaximumCall860Via861Chunk06.values_eq,
      MaximumCall860Via861Chunk07.values_eq,
      MaximumCall860Via861Chunk08.values_eq,
      MaximumCall860Via861Chunk09.values_eq,
      MaximumCall860Via861Chunk10.values_eq,
      MaximumCall860Via861Chunk11.values_eq,
      MaximumCall860Via861Chunk12.values_eq,
      MaximumCall860Via861Chunk13.values_eq,
      MaximumCall860Via861Chunk14.values_eq,
      MaximumCall860Via861Chunk15.values_eq,
      MaximumCall860Via861Chunk16.values_eq,
      MaximumCall860Via861Chunk17.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
