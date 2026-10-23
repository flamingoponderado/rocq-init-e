From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall606Via625Context.

Definition values := Eval vm_compute in List.map MaximumCall606Via625Context.depth (List.firstn 2 (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via625Context.leaves))).
Lemma values_eq : List.map MaximumCall606Via625Context.depth (List.firstn 2 (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via625Context.leaves))) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
