From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall625Via860ContextFrom861.

Definition values := Eval vm_compute in List.map MaximumCall625Via860ContextFrom861.depth (List.skipn 5 (List.skipn 1 (MaximumListChunks.chunk_at 1 MaximumCall625Via860ContextFrom861.leaves))).
Lemma values_eq : List.map MaximumCall625Via860ContextFrom861.depth (List.skipn 5 (List.skipn 1 (MaximumListChunks.chunk_at 1 MaximumCall625Via860ContextFrom861.leaves))) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
