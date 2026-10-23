From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall598StructuredFrom616From617Context MaximumCall598StructuredFrom616From617Chunk00 MaximumCall598StructuredFrom616From617Chunk01 MaximumCall598StructuredFrom616From617Chunk02 MaximumCall598StructuredFrom616From617Chunk03 MaximumCall598StructuredFrom616From617Chunk04 MaximumCall598StructuredFrom616From617Chunk05 MaximumCall598StructuredFrom616From617Chunk06 MaximumCall598StructuredFrom616From617Chunk07 MaximumCall598StructuredFrom616From617Chunk08 MaximumCall598StructuredFrom616From617Chunk09 MaximumCall598StructuredFrom616From617Chunk10 MaximumCall598StructuredFrom616From617Chunk11.

Definition values :=
  MaximumCall598StructuredFrom616From617Chunk00.values ++
  MaximumCall598StructuredFrom616From617Chunk01.values ++
  MaximumCall598StructuredFrom616From617Chunk02.values ++
  MaximumCall598StructuredFrom616From617Chunk03.values ++
  MaximumCall598StructuredFrom616From617Chunk04.values ++
  MaximumCall598StructuredFrom616From617Chunk05.values ++
  MaximumCall598StructuredFrom616From617Chunk06.values ++
  MaximumCall598StructuredFrom616From617Chunk07.values ++
  MaximumCall598StructuredFrom616From617Chunk08.values ++
  MaximumCall598StructuredFrom616From617Chunk09.values ++
  MaximumCall598StructuredFrom616From617Chunk10.values ++
  MaximumCall598StructuredFrom616From617Chunk11.values.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom616From617Context.depth MaximumCall598StructuredFrom616From617Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 12
    MaximumCall598StructuredFrom616From617Context.depth MaximumCall598StructuredFrom616From617Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall598StructuredFrom616From617Chunk00.values_eq,
      MaximumCall598StructuredFrom616From617Chunk01.values_eq,
      MaximumCall598StructuredFrom616From617Chunk02.values_eq,
      MaximumCall598StructuredFrom616From617Chunk03.values_eq,
      MaximumCall598StructuredFrom616From617Chunk04.values_eq,
      MaximumCall598StructuredFrom616From617Chunk05.values_eq,
      MaximumCall598StructuredFrom616From617Chunk06.values_eq,
      MaximumCall598StructuredFrom616From617Chunk07.values_eq,
      MaximumCall598StructuredFrom616From617Chunk08.values_eq,
      MaximumCall598StructuredFrom616From617Chunk09.values_eq,
      MaximumCall598StructuredFrom616From617Chunk10.values_eq,
      MaximumCall598StructuredFrom616From617Chunk11.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
