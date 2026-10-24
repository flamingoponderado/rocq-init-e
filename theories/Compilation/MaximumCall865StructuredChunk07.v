From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall865StructuredContext.
Definition values := Eval vm_compute in List.map MaximumCall865StructuredContext.depth (MaximumListChunks.chunk_at 7 MaximumCall865StructuredContext.leaves).
Lemma values_eq : List.map MaximumCall865StructuredContext.depth (MaximumListChunks.chunk_at 7 MaximumCall865StructuredContext.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
