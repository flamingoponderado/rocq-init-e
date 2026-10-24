From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall617Via595ContextFrom608.

Definition values := Eval vm_compute in
  List.map MaximumCall617Via595ContextFrom608.depth
    (List.firstn 3 (MaximumListChunks.chunk_at 7 MaximumCall617Via595ContextFrom608.leaves)).
Lemma values_eq :
  List.map MaximumCall617Via595ContextFrom608.depth
    (List.firstn 3 (MaximumListChunks.chunk_at 7 MaximumCall617Via595ContextFrom608.leaves)) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
