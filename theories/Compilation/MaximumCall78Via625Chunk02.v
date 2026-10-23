From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall78Via625Context.

Definition values := Eval vm_compute in List.map MaximumCall78Via625Context.depth
  (MaximumListChunks.chunk_at 2 MaximumCall78Via625Context.leaves).
Lemma values_eq :
  List.map MaximumCall78Via625Context.depth
    (MaximumListChunks.chunk_at 2 MaximumCall78Via625Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
