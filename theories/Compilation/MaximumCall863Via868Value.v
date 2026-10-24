From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall863Via868Context MaximumCall863Via868Chunk00 MaximumCall863Via868Chunk01 MaximumCall863Via868Chunk02 MaximumCall863Via868Chunk03 MaximumCall863Via868Chunk04 MaximumCall863Via868Chunk05 MaximumCall863Via868Chunk06 MaximumCall863Via868Chunk07 MaximumCall863Via868Chunk08 MaximumCall863Via868Chunk09 MaximumCall863Via868Chunk10 MaximumCall863Via868Chunk11 MaximumCall863Via868Chunk12 MaximumCall863Via868Chunk13 MaximumCall863Via868Chunk14 MaximumCall863Via868Chunk15 MaximumCall863Via868Chunk16 MaximumCall863Via868Chunk17 MaximumCall863Via868Chunk18 MaximumCall863Via868Chunk19 MaximumCall863Via868Chunk20 MaximumCall863Via868Chunk21 MaximumCall863Via868Chunk22 MaximumCall863Via868Chunk23 MaximumCall863Via868Chunk24 MaximumCall863Via868Chunk25 MaximumCall863Via868Chunk26 MaximumCall863Via868Chunk27 MaximumCall863Via868Chunk28 MaximumCall863Via868Chunk29 MaximumCall863Via868Chunk30 MaximumCall863Via868Chunk31 MaximumCall863Via868Chunk32 MaximumCall863Via868Chunk33 MaximumCall863Via868Chunk34 MaximumCall863Via868Chunk35 MaximumCall863Via868Chunk36 MaximumCall863Via868Chunk37 MaximumCall863Via868Chunk38 MaximumCall863Via868Chunk39 MaximumCall863Via868Chunk40 MaximumCall863Via868Chunk41 MaximumCall863Via868Chunk42 MaximumCall863Via868Chunk43 MaximumCall863Via868Chunk44 MaximumCall863Via868Chunk45 MaximumCall863Via868Chunk46 MaximumCall863Via868Chunk47 MaximumCall863Via868Chunk48 MaximumCall863Via868Chunk49 MaximumCall863Via868Chunk50 MaximumCall863Via868Chunk51 MaximumCall863Via868Chunk52 MaximumCall863Via868Chunk53 MaximumCall863Via868Chunk54 MaximumCall863Via868Chunk55 MaximumCall863Via868Chunk56 MaximumCall863Via868Chunk57 MaximumCall863Via868Chunk58 MaximumCall863Via868Chunk59 MaximumCall863Via868Chunk60 MaximumCall863Via868Chunk61 MaximumCall863Via868Chunk62 MaximumCall863Via868Chunk63 MaximumCall863Via868Chunk64 MaximumCall863Via868Chunk65 MaximumCall863Via868Chunk66 MaximumCall863Via868Chunk67 MaximumCall863Via868Chunk68 MaximumCall863Via868Chunk69 MaximumCall863Via868Chunk70.

Definition values :=
  MaximumCall863Via868Chunk00.values ++
  MaximumCall863Via868Chunk01.values ++
  MaximumCall863Via868Chunk02.values ++
  MaximumCall863Via868Chunk03.values ++
  MaximumCall863Via868Chunk04.values ++
  MaximumCall863Via868Chunk05.values ++
  MaximumCall863Via868Chunk06.values ++
  MaximumCall863Via868Chunk07.values ++
  MaximumCall863Via868Chunk08.values ++
  MaximumCall863Via868Chunk09.values ++
  MaximumCall863Via868Chunk10.values ++
  MaximumCall863Via868Chunk11.values ++
  MaximumCall863Via868Chunk12.values ++
  MaximumCall863Via868Chunk13.values ++
  MaximumCall863Via868Chunk14.values ++
  MaximumCall863Via868Chunk15.values ++
  MaximumCall863Via868Chunk16.values ++
  MaximumCall863Via868Chunk17.values ++
  MaximumCall863Via868Chunk18.values ++
  MaximumCall863Via868Chunk19.values ++
  MaximumCall863Via868Chunk20.values ++
  MaximumCall863Via868Chunk21.values ++
  MaximumCall863Via868Chunk22.values ++
  MaximumCall863Via868Chunk23.values ++
  MaximumCall863Via868Chunk24.values ++
  MaximumCall863Via868Chunk25.values ++
  MaximumCall863Via868Chunk26.values ++
  MaximumCall863Via868Chunk27.values ++
  MaximumCall863Via868Chunk28.values ++
  MaximumCall863Via868Chunk29.values ++
  MaximumCall863Via868Chunk30.values ++
  MaximumCall863Via868Chunk31.values ++
  MaximumCall863Via868Chunk32.values ++
  MaximumCall863Via868Chunk33.values ++
  MaximumCall863Via868Chunk34.values ++
  MaximumCall863Via868Chunk35.values ++
  MaximumCall863Via868Chunk36.values ++
  MaximumCall863Via868Chunk37.values ++
  MaximumCall863Via868Chunk38.values ++
  MaximumCall863Via868Chunk39.values ++
  MaximumCall863Via868Chunk40.values ++
  MaximumCall863Via868Chunk41.values ++
  MaximumCall863Via868Chunk42.values ++
  MaximumCall863Via868Chunk43.values ++
  MaximumCall863Via868Chunk44.values ++
  MaximumCall863Via868Chunk45.values ++
  MaximumCall863Via868Chunk46.values ++
  MaximumCall863Via868Chunk47.values ++
  MaximumCall863Via868Chunk48.values ++
  MaximumCall863Via868Chunk49.values ++
  MaximumCall863Via868Chunk50.values ++
  MaximumCall863Via868Chunk51.values ++
  MaximumCall863Via868Chunk52.values ++
  MaximumCall863Via868Chunk53.values ++
  MaximumCall863Via868Chunk54.values ++
  MaximumCall863Via868Chunk55.values ++
  MaximumCall863Via868Chunk56.values ++
  MaximumCall863Via868Chunk57.values ++
  MaximumCall863Via868Chunk58.values ++
  MaximumCall863Via868Chunk59.values ++
  MaximumCall863Via868Chunk60.values ++
  MaximumCall863Via868Chunk61.values ++
  MaximumCall863Via868Chunk62.values ++
  MaximumCall863Via868Chunk63.values ++
  MaximumCall863Via868Chunk64.values ++
  MaximumCall863Via868Chunk65.values ++
  MaximumCall863Via868Chunk66.values ++
  MaximumCall863Via868Chunk67.values ++
  MaximumCall863Via868Chunk68.values ++
  MaximumCall863Via868Chunk69.values ++
  MaximumCall863Via868Chunk70.values.

Lemma values_eq :
  List.map MaximumCall863Via868Context.depth MaximumCall863Via868Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 71
    MaximumCall863Via868Context.depth MaximumCall863Via868Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall863Via868Chunk00.values_eq,
      MaximumCall863Via868Chunk01.values_eq,
      MaximumCall863Via868Chunk02.values_eq,
      MaximumCall863Via868Chunk03.values_eq,
      MaximumCall863Via868Chunk04.values_eq,
      MaximumCall863Via868Chunk05.values_eq,
      MaximumCall863Via868Chunk06.values_eq,
      MaximumCall863Via868Chunk07.values_eq,
      MaximumCall863Via868Chunk08.values_eq,
      MaximumCall863Via868Chunk09.values_eq,
      MaximumCall863Via868Chunk10.values_eq,
      MaximumCall863Via868Chunk11.values_eq,
      MaximumCall863Via868Chunk12.values_eq,
      MaximumCall863Via868Chunk13.values_eq,
      MaximumCall863Via868Chunk14.values_eq,
      MaximumCall863Via868Chunk15.values_eq,
      MaximumCall863Via868Chunk16.values_eq,
      MaximumCall863Via868Chunk17.values_eq,
      MaximumCall863Via868Chunk18.values_eq,
      MaximumCall863Via868Chunk19.values_eq,
      MaximumCall863Via868Chunk20.values_eq,
      MaximumCall863Via868Chunk21.values_eq,
      MaximumCall863Via868Chunk22.values_eq,
      MaximumCall863Via868Chunk23.values_eq,
      MaximumCall863Via868Chunk24.values_eq,
      MaximumCall863Via868Chunk25.values_eq,
      MaximumCall863Via868Chunk26.values_eq,
      MaximumCall863Via868Chunk27.values_eq,
      MaximumCall863Via868Chunk28.values_eq,
      MaximumCall863Via868Chunk29.values_eq,
      MaximumCall863Via868Chunk30.values_eq,
      MaximumCall863Via868Chunk31.values_eq,
      MaximumCall863Via868Chunk32.values_eq,
      MaximumCall863Via868Chunk33.values_eq,
      MaximumCall863Via868Chunk34.values_eq,
      MaximumCall863Via868Chunk35.values_eq,
      MaximumCall863Via868Chunk36.values_eq,
      MaximumCall863Via868Chunk37.values_eq,
      MaximumCall863Via868Chunk38.values_eq,
      MaximumCall863Via868Chunk39.values_eq,
      MaximumCall863Via868Chunk40.values_eq,
      MaximumCall863Via868Chunk41.values_eq,
      MaximumCall863Via868Chunk42.values_eq,
      MaximumCall863Via868Chunk43.values_eq,
      MaximumCall863Via868Chunk44.values_eq,
      MaximumCall863Via868Chunk45.values_eq,
      MaximumCall863Via868Chunk46.values_eq,
      MaximumCall863Via868Chunk47.values_eq,
      MaximumCall863Via868Chunk48.values_eq,
      MaximumCall863Via868Chunk49.values_eq,
      MaximumCall863Via868Chunk50.values_eq,
      MaximumCall863Via868Chunk51.values_eq,
      MaximumCall863Via868Chunk52.values_eq,
      MaximumCall863Via868Chunk53.values_eq,
      MaximumCall863Via868Chunk54.values_eq,
      MaximumCall863Via868Chunk55.values_eq,
      MaximumCall863Via868Chunk56.values_eq,
      MaximumCall863Via868Chunk57.values_eq,
      MaximumCall863Via868Chunk58.values_eq,
      MaximumCall863Via868Chunk59.values_eq,
      MaximumCall863Via868Chunk60.values_eq,
      MaximumCall863Via868Chunk61.values_eq,
      MaximumCall863Via868Chunk62.values_eq,
      MaximumCall863Via868Chunk63.values_eq,
      MaximumCall863Via868Chunk64.values_eq,
      MaximumCall863Via868Chunk65.values_eq,
      MaximumCall863Via868Chunk66.values_eq,
      MaximumCall863Via868Chunk67.values_eq,
      MaximumCall863Via868Chunk68.values_eq,
      MaximumCall863Via868Chunk69.values_eq,
      MaximumCall863Via868Chunk70.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
