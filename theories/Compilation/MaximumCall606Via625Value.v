From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall606Via625Context MaximumCall606Via625Chunk00 MaximumCall606Via625Chunk01 MaximumCall606Via625Chunk02 MaximumCall606Via625Chunk03 MaximumCall606Via625Chunk04 MaximumCall606Via625Chunk05.

Definition values :=
  MaximumCall606Via625Chunk00.values ++
  MaximumCall606Via625Chunk01.values ++
  MaximumCall606Via625Chunk02.values ++
  MaximumCall606Via625Chunk03.values ++
  MaximumCall606Via625Chunk04.values ++
  MaximumCall606Via625Chunk05.values.

Lemma values_eq :
  List.map MaximumCall606Via625Context.depth MaximumCall606Via625Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 6
    MaximumCall606Via625Context.depth MaximumCall606Via625Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall606Via625Chunk00.values_eq,
      MaximumCall606Via625Chunk01.values_eq,
      MaximumCall606Via625Chunk02.values_eq,
      MaximumCall606Via625Chunk03.values_eq,
      MaximumCall606Via625Chunk04.values_eq,
      MaximumCall606Via625Chunk05.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
