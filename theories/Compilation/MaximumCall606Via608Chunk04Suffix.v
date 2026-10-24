From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall606Via608Context.

Definition values := Eval vm_compute in List.map MaximumCall606Via608Context.depth (List.skipn 3 (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via608Context.leaves))).
Lemma values_eq : List.map MaximumCall606Via608Context.depth (List.skipn 3 (List.skipn 3 (MaximumListChunks.chunk_at 4 MaximumCall606Via608Context.leaves))) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
