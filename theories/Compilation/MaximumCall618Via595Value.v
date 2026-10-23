From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall618Via595Context MaximumCall618Via595Chunk00 MaximumCall618Via595Chunk01 MaximumCall618Via595Chunk02 MaximumCall618Via595Chunk03 MaximumCall618Via595Chunk04 MaximumCall618Via595Chunk05 MaximumCall618Via595Chunk06 MaximumCall618Via595Chunk07 MaximumCall618Via595Chunk08 MaximumCall618Via595Chunk09 MaximumCall618Via595Chunk10.

Definition values :=
  MaximumCall618Via595Chunk00.values ++
  MaximumCall618Via595Chunk01.values ++
  MaximumCall618Via595Chunk02.values ++
  MaximumCall618Via595Chunk03.values ++
  MaximumCall618Via595Chunk04.values ++
  MaximumCall618Via595Chunk05.values ++
  MaximumCall618Via595Chunk06.values ++
  MaximumCall618Via595Chunk07.values ++
  MaximumCall618Via595Chunk08.values ++
  MaximumCall618Via595Chunk09.values ++
  MaximumCall618Via595Chunk10.values.

Lemma values_eq :
  List.map MaximumCall618Via595Context.depth MaximumCall618Via595Context.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 11
    MaximumCall618Via595Context.depth MaximumCall618Via595Context.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall618Via595Chunk00.values_eq,
      MaximumCall618Via595Chunk01.values_eq,
      MaximumCall618Via595Chunk02.values_eq,
      MaximumCall618Via595Chunk03.values_eq,
      MaximumCall618Via595Chunk04.values_eq,
      MaximumCall618Via595Chunk05.values_eq,
      MaximumCall618Via595Chunk06.values_eq,
      MaximumCall618Via595Chunk07.values_eq,
      MaximumCall618Via595Chunk08.values_eq,
      MaximumCall618Via595Chunk09.values_eq,
      MaximumCall618Via595Chunk10.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
