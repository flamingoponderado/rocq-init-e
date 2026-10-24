From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall602Via606ContextFrom608From860.

Definition values := Eval vm_compute in
  List.map MaximumCall602Via606ContextFrom608From860.depth
    (List.firstn 4 (MaximumListChunks.chunk_at 0 MaximumCall602Via606ContextFrom608From860.leaves)).
Lemma values_eq :
  List.map MaximumCall602Via606ContextFrom608From860.depth
    (List.firstn 4 (MaximumListChunks.chunk_at 0 MaximumCall602Via606ContextFrom608From860.leaves)) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
