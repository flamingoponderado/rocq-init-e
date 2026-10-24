From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall624Via595ContextFrom608From860.

Definition values := Eval vm_compute in List.map MaximumCall624Via595ContextFrom608From860.depth
  (MaximumListChunks.chunk_at 2 MaximumCall624Via595ContextFrom608From860.leaves).
Lemma values_eq :
  List.map MaximumCall624Via595ContextFrom608From860.depth
    (MaximumListChunks.chunk_at 2 MaximumCall624Via595ContextFrom608From860.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
