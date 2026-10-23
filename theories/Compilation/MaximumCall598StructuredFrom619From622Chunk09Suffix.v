From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall598StructuredFrom619From622Context.

Definition values := Eval vm_compute in
  List.map MaximumCall598StructuredFrom619From622Context.depth
    (List.skipn 6 (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom619From622Context.leaves)).
Lemma values_eq :
  List.map MaximumCall598StructuredFrom619From622Context.depth
    (List.skipn 6 (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom619From622Context.leaves)) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
