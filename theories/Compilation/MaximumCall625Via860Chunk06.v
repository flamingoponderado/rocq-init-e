From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall625Via860Context.

Definition values := Eval vm_compute in List.map MaximumCall625Via860Context.depth
  (MaximumListChunks.chunk_at 6 MaximumCall625Via860Context.leaves).
Lemma values_eq :
  List.map MaximumCall625Via860Context.depth
    (MaximumListChunks.chunk_at 6 MaximumCall625Via860Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
