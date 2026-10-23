From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall602Via606Context.

Definition values := Eval vm_compute in List.map MaximumCall602Via606Context.depth
  (MaximumListChunks.chunk_at 1 MaximumCall602Via606Context.leaves).
Lemma values_eq :
  List.map MaximumCall602Via606Context.depth
    (MaximumListChunks.chunk_at 1 MaximumCall602Via606Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
