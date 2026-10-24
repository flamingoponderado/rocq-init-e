From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumContext.
Definition values := Eval vm_compute in List.map MaximumContext.depth (MaximumListChunks.chunk_at 38 MaximumContext.leaves).
Lemma values_eq : List.map MaximumContext.depth (MaximumListChunks.chunk_at 38 MaximumContext.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
