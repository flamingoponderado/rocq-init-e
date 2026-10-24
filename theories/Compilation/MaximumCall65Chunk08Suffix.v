From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall65Context.

Definition values := Eval vm_compute in
  List.map MaximumCall65Context.depth
    (List.skipn 3 (MaximumListChunks.chunk_at 8 MaximumCall65Context.leaves)).
Lemma values_eq :
  List.map MaximumCall65Context.depth
    (List.skipn 3 (MaximumListChunks.chunk_at 8 MaximumCall65Context.leaves)) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
