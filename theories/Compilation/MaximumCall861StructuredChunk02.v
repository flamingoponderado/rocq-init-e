From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall861StructuredContext.
Definition values := Eval vm_compute in List.map MaximumCall861StructuredContext.depth (MaximumListChunks.chunk_at 2 MaximumCall861StructuredContext.leaves).
Lemma values_eq : List.map MaximumCall861StructuredContext.depth (MaximumListChunks.chunk_at 2 MaximumCall861StructuredContext.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
