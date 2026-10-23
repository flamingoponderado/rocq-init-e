From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall619Via623Context.

Definition values := Eval vm_compute in List.map MaximumCall619Via623Context.depth
  (MaximumListChunks.chunk_at 2 MaximumCall619Via623Context.leaves).
Lemma values_eq :
  List.map MaximumCall619Via623Context.depth
    (MaximumListChunks.chunk_at 2 MaximumCall619Via623Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
