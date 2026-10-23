From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall615Via618Context.

Definition values := Eval vm_compute in List.map MaximumCall615Via618Context.depth
  (MaximumListChunks.chunk_at 5 MaximumCall615Via618Context.leaves).
Lemma values_eq :
  List.map MaximumCall615Via618Context.depth
    (MaximumListChunks.chunk_at 5 MaximumCall615Via618Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
