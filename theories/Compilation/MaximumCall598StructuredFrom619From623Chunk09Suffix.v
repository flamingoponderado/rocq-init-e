From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall598StructuredFrom619From623Context.

Definition values := Eval vm_compute in
  List.map MaximumCall598StructuredFrom619From623Context.depth
    (List.skipn 6 (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom619From623Context.leaves)).
Lemma values_eq :
  List.map MaximumCall598StructuredFrom619From623Context.depth
    (List.skipn 6 (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom619From623Context.leaves)) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
