From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall837StructuredFrom598From619From621ContextFrom860.

Definition values := Eval vm_compute in List.map MaximumCall837StructuredFrom598From619From621ContextFrom860.depth
  (MaximumListChunks.chunk_at 6 MaximumCall837StructuredFrom598From619From621ContextFrom860.leaves).
Lemma values_eq :
  List.map MaximumCall837StructuredFrom598From619From621ContextFrom860.depth
    (MaximumListChunks.chunk_at 6 MaximumCall837StructuredFrom598From619From621ContextFrom860.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
