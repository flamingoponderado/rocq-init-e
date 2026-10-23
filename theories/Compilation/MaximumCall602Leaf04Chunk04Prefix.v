From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall602Leaf04Context.

Definition values := Eval vm_compute in
  List.map MaximumCall602Leaf04Context.depth
    (List.firstn 3 (MaximumListChunks.chunk_at 4 MaximumCall602Leaf04Context.leaves)).
Lemma values_eq :
  List.map MaximumCall602Leaf04Context.depth
    (List.firstn 3 (MaximumListChunks.chunk_at 4 MaximumCall602Leaf04Context.leaves)) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
