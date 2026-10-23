From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall619Via624Context.

Definition values := Eval vm_compute in List.map MaximumCall619Via624Context.depth
  (MaximumListChunks.chunk_at 4 MaximumCall619Via624Context.leaves).
Lemma values_eq :
  List.map MaximumCall619Via624Context.depth
    (MaximumListChunks.chunk_at 4 MaximumCall619Via624Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
