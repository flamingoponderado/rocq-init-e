From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall868Context MaximumCall868Pieces.

Definition values := Eval vm_compute in List.map MaximumCall868Context.depth (MaximumListChunks.chunk_at 36 MaximumCall868Pieces.suffix).
Lemma values_eq : List.map MaximumCall868Context.depth (MaximumListChunks.chunk_at 36 MaximumCall868Pieces.suffix) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
