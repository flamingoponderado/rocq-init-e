From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall603Via616From617Context MaximumCall603Via616From617Chunk00 MaximumCall603Via616From617Chunk01 MaximumCall603Via616From617Chunk02 MaximumCall603Via616From617Chunk03 MaximumCall603Via616From617Chunk04 MaximumCall603Via616From617Chunk05 MaximumCall603Via616From617Chunk06 MaximumCall603Via616From617Chunk07 MaximumCall603Via616From617Chunk08.

Definition values :=
  MaximumCall603Via616From617Chunk00.values ++
  MaximumCall603Via616From617Chunk01.values ++
  MaximumCall603Via616From617Chunk02.values ++
  MaximumCall603Via616From617Chunk03.values ++
  MaximumCall603Via616From617Chunk04.values ++
  MaximumCall603Via616From617Chunk05.values ++
  MaximumCall603Via616From617Chunk06.values ++
  MaximumCall603Via616From617Chunk07.values ++
  MaximumCall603Via616From617Chunk08.values.

Lemma values_eq :
  List.map MaximumCall603Via616From617Context.depth MaximumCall603Via616From617Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 9
    MaximumCall603Via616From617Context.depth MaximumCall603Via616From617Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall603Via616From617Chunk00.values_eq,
      MaximumCall603Via616From617Chunk01.values_eq,
      MaximumCall603Via616From617Chunk02.values_eq,
      MaximumCall603Via616From617Chunk03.values_eq,
      MaximumCall603Via616From617Chunk04.values_eq,
      MaximumCall603Via616From617Chunk05.values_eq,
      MaximumCall603Via616From617Chunk06.values_eq,
      MaximumCall603Via616From617Chunk07.values_eq,
      MaximumCall603Via616From617Chunk08.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
