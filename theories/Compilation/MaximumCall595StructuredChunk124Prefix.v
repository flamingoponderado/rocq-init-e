From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall595StructuredContext.

Definition values := Eval vm_compute in
  List.map MaximumCall595StructuredContext.depth
    (List.firstn 3 (MaximumListChunks.chunk_at 124 MaximumCall595StructuredContext.leaves)).
Lemma values_eq :
  List.map MaximumCall595StructuredContext.depth
    (List.firstn 3 (MaximumListChunks.chunk_at 124 MaximumCall595StructuredContext.leaves)) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
