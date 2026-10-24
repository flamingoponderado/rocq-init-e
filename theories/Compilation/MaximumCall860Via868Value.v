From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall860Via868Context MaximumCall860Via868Chunk00 MaximumCall860Via868Chunk01 MaximumCall860Via868Chunk02 MaximumCall860Via868Chunk03 MaximumCall860Via868Chunk04 MaximumCall860Via868Chunk05 MaximumCall860Via868Chunk06 MaximumCall860Via868Chunk07 MaximumCall860Via868Chunk08 MaximumCall860Via868Chunk09 MaximumCall860Via868Chunk10 MaximumCall860Via868Chunk11 MaximumCall860Via868Chunk12 MaximumCall860Via868Chunk13 MaximumCall860Via868Chunk14 MaximumCall860Via868Chunk15 MaximumCall860Via868Chunk16 MaximumCall860Via868Chunk17.

Definition values :=
  MaximumCall860Via868Chunk00.values ++
  MaximumCall860Via868Chunk01.values ++
  MaximumCall860Via868Chunk02.values ++
  MaximumCall860Via868Chunk03.values ++
  MaximumCall860Via868Chunk04.values ++
  MaximumCall860Via868Chunk05.values ++
  MaximumCall860Via868Chunk06.values ++
  MaximumCall860Via868Chunk07.values ++
  MaximumCall860Via868Chunk08.values ++
  MaximumCall860Via868Chunk09.values ++
  MaximumCall860Via868Chunk10.values ++
  MaximumCall860Via868Chunk11.values ++
  MaximumCall860Via868Chunk12.values ++
  MaximumCall860Via868Chunk13.values ++
  MaximumCall860Via868Chunk14.values ++
  MaximumCall860Via868Chunk15.values ++
  MaximumCall860Via868Chunk16.values ++
  MaximumCall860Via868Chunk17.values.

Lemma values_eq :
  List.map MaximumCall860Via868Context.depth MaximumCall860Via868Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 18
    MaximumCall860Via868Context.depth MaximumCall860Via868Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall860Via868Chunk00.values_eq,
      MaximumCall860Via868Chunk01.values_eq,
      MaximumCall860Via868Chunk02.values_eq,
      MaximumCall860Via868Chunk03.values_eq,
      MaximumCall860Via868Chunk04.values_eq,
      MaximumCall860Via868Chunk05.values_eq,
      MaximumCall860Via868Chunk06.values_eq,
      MaximumCall860Via868Chunk07.values_eq,
      MaximumCall860Via868Chunk08.values_eq,
      MaximumCall860Via868Chunk09.values_eq,
      MaximumCall860Via868Chunk10.values_eq,
      MaximumCall860Via868Chunk11.values_eq,
      MaximumCall860Via868Chunk12.values_eq,
      MaximumCall860Via868Chunk13.values_eq,
      MaximumCall860Via868Chunk14.values_eq,
      MaximumCall860Via868Chunk15.values_eq,
      MaximumCall860Via868Chunk16.values_eq,
      MaximumCall860Via868Chunk17.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
