From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall618Via595ContextFrom608 MaximumCall618Via595Chunk00From608 MaximumCall618Via595Chunk01From608 MaximumCall618Via595Chunk02From608 MaximumCall618Via595Chunk03From608 MaximumCall618Via595Chunk04From608 MaximumCall618Via595Chunk05From608 MaximumCall618Via595Chunk06From608 MaximumCall618Via595Chunk07From608 MaximumCall618Via595Chunk08From608 MaximumCall618Via595Chunk09From608 MaximumCall618Via595Chunk10From608.

Definition values :=
  MaximumCall618Via595Chunk00From608.values ++
  MaximumCall618Via595Chunk01From608.values ++
  MaximumCall618Via595Chunk02From608.values ++
  MaximumCall618Via595Chunk03From608.values ++
  MaximumCall618Via595Chunk04From608.values ++
  MaximumCall618Via595Chunk05From608.values ++
  MaximumCall618Via595Chunk06From608.values ++
  MaximumCall618Via595Chunk07From608.values ++
  MaximumCall618Via595Chunk08From608.values ++
  MaximumCall618Via595Chunk09From608.values ++
  MaximumCall618Via595Chunk10From608.values.

Lemma values_eq :
  List.map MaximumCall618Via595ContextFrom608.depth MaximumCall618Via595ContextFrom608.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 11
    MaximumCall618Via595ContextFrom608.depth MaximumCall618Via595ContextFrom608.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall618Via595Chunk00From608.values_eq,
      MaximumCall618Via595Chunk01From608.values_eq,
      MaximumCall618Via595Chunk02From608.values_eq,
      MaximumCall618Via595Chunk03From608.values_eq,
      MaximumCall618Via595Chunk04From608.values_eq,
      MaximumCall618Via595Chunk05From608.values_eq,
      MaximumCall618Via595Chunk06From608.values_eq,
      MaximumCall618Via595Chunk07From608.values_eq,
      MaximumCall618Via595Chunk08From608.values_eq,
      MaximumCall618Via595Chunk09From608.values_eq,
      MaximumCall618Via595Chunk10From608.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
