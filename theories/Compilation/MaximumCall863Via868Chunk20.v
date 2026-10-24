From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall863Via868Context.

Definition values := Eval vm_compute in List.map MaximumCall863Via868Context.depth
  (MaximumListChunks.chunk_at 20 MaximumCall863Via868Context.leaves).
Lemma values_eq :
  List.map MaximumCall863Via868Context.depth
    (MaximumListChunks.chunk_at 20 MaximumCall863Via868Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
