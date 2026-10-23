From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall612Via616From618Context MaximumCall612Via616From618Chunk00 MaximumCall612Via616From618Chunk01 MaximumCall612Via616From618Chunk02 MaximumCall612Via616From618Chunk03 MaximumCall612Via616From618Chunk04 MaximumCall612Via616From618Chunk05 MaximumCall612Via616From618Chunk06 MaximumCall612Via616From618Chunk07 MaximumCall612Via616From618Chunk08 MaximumCall612Via616From618Chunk09 MaximumCall612Via616From618Chunk10 MaximumCall612Via616From618Chunk11 MaximumCall612Via616From618Chunk12 MaximumCall612Via616From618Chunk13.

Definition values :=
  MaximumCall612Via616From618Chunk00.values ++
  MaximumCall612Via616From618Chunk01.values ++
  MaximumCall612Via616From618Chunk02.values ++
  MaximumCall612Via616From618Chunk03.values ++
  MaximumCall612Via616From618Chunk04.values ++
  MaximumCall612Via616From618Chunk05.values ++
  MaximumCall612Via616From618Chunk06.values ++
  MaximumCall612Via616From618Chunk07.values ++
  MaximumCall612Via616From618Chunk08.values ++
  MaximumCall612Via616From618Chunk09.values ++
  MaximumCall612Via616From618Chunk10.values ++
  MaximumCall612Via616From618Chunk11.values ++
  MaximumCall612Via616From618Chunk12.values ++
  MaximumCall612Via616From618Chunk13.values.

Lemma values_eq :
  List.map MaximumCall612Via616From618Context.depth MaximumCall612Via616From618Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 14
    MaximumCall612Via616From618Context.depth MaximumCall612Via616From618Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall612Via616From618Chunk00.values_eq,
      MaximumCall612Via616From618Chunk01.values_eq,
      MaximumCall612Via616From618Chunk02.values_eq,
      MaximumCall612Via616From618Chunk03.values_eq,
      MaximumCall612Via616From618Chunk04.values_eq,
      MaximumCall612Via616From618Chunk05.values_eq,
      MaximumCall612Via616From618Chunk06.values_eq,
      MaximumCall612Via616From618Chunk07.values_eq,
      MaximumCall612Via616From618Chunk08.values_eq,
      MaximumCall612Via616From618Chunk09.values_eq,
      MaximumCall612Via616From618Chunk10.values_eq,
      MaximumCall612Via616From618Chunk11.values_eq,
      MaximumCall612Via616From618Chunk12.values_eq,
      MaximumCall612Via616From618Chunk13.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
