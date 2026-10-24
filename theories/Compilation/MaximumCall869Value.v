From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall869SuffixContext MaximumCall869Chunk00 MaximumCall869Chunk01 MaximumCall869Chunk02 MaximumCall869Chunk03 MaximumCall869Chunk04 MaximumCall869Chunk05 MaximumCall869Chunk06 MaximumCall869Chunk07 MaximumCall869Chunk08 MaximumCall869Chunk09 MaximumCall869Chunk10 MaximumCall869Chunk11 MaximumCall869Chunk12 MaximumCall869Chunk13 MaximumCall869Chunk14 MaximumCall869Chunk15 MaximumCall869Chunk16 MaximumCall869Chunk17 MaximumCall869Chunk18 MaximumCall869Chunk19 MaximumCall869Chunk20 MaximumCall869Chunk21 MaximumCall869Chunk22 MaximumCall869Chunk23 MaximumCall869Chunk24 MaximumCall869Chunk25 MaximumCall869Chunk26.

Definition values :=
  MaximumCall869Chunk00.values ++
  MaximumCall869Chunk01.values ++
  MaximumCall869Chunk02.values ++
  MaximumCall869Chunk03.values ++
  MaximumCall869Chunk04.values ++
  MaximumCall869Chunk05.values ++
  MaximumCall869Chunk06.values ++
  MaximumCall869Chunk07.values ++
  MaximumCall869Chunk08.values ++
  MaximumCall869Chunk09.values ++
  MaximumCall869Chunk10.values ++
  MaximumCall869Chunk11.values ++
  MaximumCall869Chunk12.values ++
  MaximumCall869Chunk13.values ++
  MaximumCall869Chunk14.values ++
  MaximumCall869Chunk15.values ++
  MaximumCall869Chunk16.values ++
  MaximumCall869Chunk17.values ++
  MaximumCall869Chunk18.values ++
  MaximumCall869Chunk19.values ++
  MaximumCall869Chunk20.values ++
  MaximumCall869Chunk21.values ++
  MaximumCall869Chunk22.values ++
  MaximumCall869Chunk23.values ++
  MaximumCall869Chunk24.values ++
  MaximumCall869Chunk25.values ++
  MaximumCall869Chunk26.values.

Lemma values_eq :
  List.map MaximumCall869SuffixContext.depth MaximumCall869SuffixContext.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 27
    MaximumCall869SuffixContext.depth MaximumCall869SuffixContext.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    unfold MaximumCall869SuffixContext.depth, MaximumCall869SuffixContext.leaves.
    rewrite MaximumCall869Chunk00.values_eq,
      MaximumCall869Chunk01.values_eq,
      MaximumCall869Chunk02.values_eq,
      MaximumCall869Chunk03.values_eq,
      MaximumCall869Chunk04.values_eq,
      MaximumCall869Chunk05.values_eq,
      MaximumCall869Chunk06.values_eq,
      MaximumCall869Chunk07.values_eq,
      MaximumCall869Chunk08.values_eq,
      MaximumCall869Chunk09.values_eq,
      MaximumCall869Chunk10.values_eq,
      MaximumCall869Chunk11.values_eq,
      MaximumCall869Chunk12.values_eq,
      MaximumCall869Chunk13.values_eq,
      MaximumCall869Chunk14.values_eq,
      MaximumCall869Chunk15.values_eq,
      MaximumCall869Chunk16.values_eq,
      MaximumCall869Chunk17.values_eq,
      MaximumCall869Chunk18.values_eq,
      MaximumCall869Chunk19.values_eq,
      MaximumCall869Chunk20.values_eq,
      MaximumCall869Chunk21.values_eq,
      MaximumCall869Chunk22.values_eq,
      MaximumCall869Chunk23.values_eq,
      MaximumCall869Chunk24.values_eq,
      MaximumCall869Chunk25.values_eq,
      MaximumCall869Chunk26.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
