From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall618Via595Context.

Definition values := Eval vm_compute in List.map MaximumCall618Via595Context.depth (List.firstn 2 (List.skipn 1 (MaximumListChunks.chunk_at 9 MaximumCall618Via595Context.leaves))).
Lemma values_eq : List.map MaximumCall618Via595Context.depth (List.firstn 2 (List.skipn 1 (MaximumListChunks.chunk_at 9 MaximumCall618Via595Context.leaves))) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
