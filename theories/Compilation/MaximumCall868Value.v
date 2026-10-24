From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall868SuffixContext MaximumCall868Chunk00 MaximumCall868Chunk01 MaximumCall868Chunk02 MaximumCall868Chunk03 MaximumCall868Chunk04 MaximumCall868Chunk05 MaximumCall868Chunk06 MaximumCall868Chunk07 MaximumCall868Chunk08 MaximumCall868Chunk09 MaximumCall868Chunk10 MaximumCall868Chunk11 MaximumCall868Chunk12 MaximumCall868Chunk13 MaximumCall868Chunk14 MaximumCall868Chunk15 MaximumCall868Chunk16 MaximumCall868Chunk17 MaximumCall868Chunk18 MaximumCall868Chunk19 MaximumCall868Chunk20 MaximumCall868Chunk21 MaximumCall868Chunk22 MaximumCall868Chunk23 MaximumCall868Chunk24 MaximumCall868Chunk25 MaximumCall868Chunk26 MaximumCall868Chunk27 MaximumCall868Chunk28 MaximumCall868Chunk29 MaximumCall868Chunk30 MaximumCall868Chunk31 MaximumCall868Chunk32 MaximumCall868Chunk33 MaximumCall868Chunk34 MaximumCall868Chunk35 MaximumCall868Chunk36 MaximumCall868Chunk37 MaximumCall868Chunk38 MaximumCall868Chunk39.

Definition values :=
  MaximumCall868Chunk00.values ++
  MaximumCall868Chunk01.values ++
  MaximumCall868Chunk02.values ++
  MaximumCall868Chunk03.values ++
  MaximumCall868Chunk04.values ++
  MaximumCall868Chunk05.values ++
  MaximumCall868Chunk06.values ++
  MaximumCall868Chunk07.values ++
  MaximumCall868Chunk08.values ++
  MaximumCall868Chunk09.values ++
  MaximumCall868Chunk10.values ++
  MaximumCall868Chunk11.values ++
  MaximumCall868Chunk12.values ++
  MaximumCall868Chunk13.values ++
  MaximumCall868Chunk14.values ++
  MaximumCall868Chunk15.values ++
  MaximumCall868Chunk16.values ++
  MaximumCall868Chunk17.values ++
  MaximumCall868Chunk18.values ++
  MaximumCall868Chunk19.values ++
  MaximumCall868Chunk20.values ++
  MaximumCall868Chunk21.values ++
  MaximumCall868Chunk22.values ++
  MaximumCall868Chunk23.values ++
  MaximumCall868Chunk24.values ++
  MaximumCall868Chunk25.values ++
  MaximumCall868Chunk26.values ++
  MaximumCall868Chunk27.values ++
  MaximumCall868Chunk28.values ++
  MaximumCall868Chunk29.values ++
  MaximumCall868Chunk30.values ++
  MaximumCall868Chunk31.values ++
  MaximumCall868Chunk32.values ++
  MaximumCall868Chunk33.values ++
  MaximumCall868Chunk34.values ++
  MaximumCall868Chunk35.values ++
  MaximumCall868Chunk36.values ++
  MaximumCall868Chunk37.values ++
  MaximumCall868Chunk38.values ++
  MaximumCall868Chunk39.values.

Lemma values_eq :
  List.map MaximumCall868SuffixContext.depth MaximumCall868SuffixContext.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 40
    MaximumCall868SuffixContext.depth MaximumCall868SuffixContext.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    unfold MaximumCall868SuffixContext.depth, MaximumCall868SuffixContext.leaves.
    rewrite MaximumCall868Chunk00.values_eq,
      MaximumCall868Chunk01.values_eq,
      MaximumCall868Chunk02.values_eq,
      MaximumCall868Chunk03.values_eq,
      MaximumCall868Chunk04.values_eq,
      MaximumCall868Chunk05.values_eq,
      MaximumCall868Chunk06.values_eq,
      MaximumCall868Chunk07.values_eq,
      MaximumCall868Chunk08.values_eq,
      MaximumCall868Chunk09.values_eq,
      MaximumCall868Chunk10.values_eq,
      MaximumCall868Chunk11.values_eq_old,
      MaximumCall868Chunk12.values_eq,
      MaximumCall868Chunk13.values_eq_old,
      MaximumCall868Chunk14.values_eq,
      MaximumCall868Chunk15.values_eq_old,
      MaximumCall868Chunk16.values_eq_old,
      MaximumCall868Chunk17.values_eq,
      MaximumCall868Chunk18.values_eq,
      MaximumCall868Chunk19.values_eq,
      MaximumCall868Chunk20.values_eq,
      MaximumCall868Chunk21.values_eq,
      MaximumCall868Chunk22.values_eq,
      MaximumCall868Chunk23.values_eq,
      MaximumCall868Chunk24.values_eq,
      MaximumCall868Chunk25.values_eq,
      MaximumCall868Chunk26.values_eq,
      MaximumCall868Chunk27.values_eq,
      MaximumCall868Chunk28.values_eq,
      MaximumCall868Chunk29.values_eq,
      MaximumCall868Chunk30.values_eq,
      MaximumCall868Chunk31.values_eq,
      MaximumCall868Chunk32.values_eq,
      MaximumCall868Chunk33.values_eq,
      MaximumCall868Chunk34.values_eq,
      MaximumCall868Chunk35.values_eq,
      MaximumCall868Chunk36.values_eq,
      MaximumCall868Chunk37.values_eq,
      MaximumCall868Chunk38.values_eq,
      MaximumCall868Chunk39.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
