From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall602Leaf04ContextFrom608.

Definition values := Eval vm_compute in List.map MaximumCall602Leaf04ContextFrom608.depth
  (MaximumListChunks.chunk_at 10 MaximumCall602Leaf04ContextFrom608.leaves).
Lemma values_eq :
  List.map MaximumCall602Leaf04ContextFrom608.depth
    (MaximumListChunks.chunk_at 10 MaximumCall602Leaf04ContextFrom608.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
