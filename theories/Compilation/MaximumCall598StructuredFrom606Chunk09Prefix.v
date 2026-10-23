From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall598StructuredFrom606Context.

Definition values := Eval vm_compute in
  List.map MaximumCall598StructuredFrom606Context.depth
    (List.firstn 5 (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom606Context.leaves)).
Lemma values_eq :
  List.map MaximumCall598StructuredFrom606Context.depth
    (List.firstn 5 (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom606Context.leaves)) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
