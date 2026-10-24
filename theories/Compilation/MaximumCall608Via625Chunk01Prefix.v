From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall608Via625Context.

Definition values := Eval vm_compute in
  List.map MaximumCall608Via625Context.depth
    (List.firstn 7 (MaximumListChunks.chunk_at 1 MaximumCall608Via625Context.leaves)).
Lemma values_eq :
  List.map MaximumCall608Via625Context.depth
    (List.firstn 7 (MaximumListChunks.chunk_at 1 MaximumCall608Via625Context.leaves)) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
