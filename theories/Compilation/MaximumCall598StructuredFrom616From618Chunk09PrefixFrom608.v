From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall598StructuredFrom616From618ContextFrom608.

Definition values := Eval vm_compute in
  List.map MaximumCall598StructuredFrom616From618ContextFrom608.depth
    (List.firstn 5 (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom616From618ContextFrom608.leaves)).
Lemma values_eq :
  List.map MaximumCall598StructuredFrom616From618ContextFrom608.depth
    (List.firstn 5 (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom616From618ContextFrom608.leaves)) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
