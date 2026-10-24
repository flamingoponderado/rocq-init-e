From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall387Via868Context.
Definition values := Eval vm_compute in List.map MaximumCall387Via868Context.depth (MaximumListChunks.chunk_at 10 MaximumCall387Via868Context.leaves).
Lemma values_eq : List.map MaximumCall387Via868Context.depth (MaximumListChunks.chunk_at 10 MaximumCall387Via868Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
