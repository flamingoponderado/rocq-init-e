From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall624Via595Context.

Definition values := Eval vm_compute in List.map MaximumCall624Via595Context.depth
  (MaximumListChunks.chunk_at 6 MaximumCall624Via595Context.leaves).
Lemma values_eq :
  List.map MaximumCall624Via595Context.depth
    (MaximumListChunks.chunk_at 6 MaximumCall624Via595Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
