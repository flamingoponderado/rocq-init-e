From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall603Via619From623Context.

Definition values := Eval vm_compute in List.map MaximumCall603Via619From623Context.depth
  (MaximumListChunks.chunk_at 1 MaximumCall603Via619From623Context.leaves).
Lemma values_eq :
  List.map MaximumCall603Via619From623Context.depth
    (MaximumListChunks.chunk_at 1 MaximumCall603Via619From623Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
