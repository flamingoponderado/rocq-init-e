From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall65Context.
Definition values := Eval vm_compute in List.map MaximumCall65Context.depth (MaximumListChunks.chunk_at 0 MaximumCall65Context.leaves).
Lemma values_eq : List.map MaximumCall65Context.depth (MaximumListChunks.chunk_at 0 MaximumCall65Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
