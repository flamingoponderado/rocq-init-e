From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall595StructuredContextFrom608.

Definition values := Eval vm_compute in
  List.map MaximumCall595StructuredContextFrom608.depth
    (List.skipn 8 (MaximumListChunks.chunk_at 131 MaximumCall595StructuredContextFrom608.leaves)).
Lemma values_eq :
  List.map MaximumCall595StructuredContextFrom608.depth
    (List.skipn 8 (MaximumListChunks.chunk_at 131 MaximumCall595StructuredContextFrom608.leaves)) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
