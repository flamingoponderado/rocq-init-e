From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall598StructuredFrom616From618Context.

Definition values := Eval vm_compute in List.map MaximumCall598StructuredFrom616From618Context.depth
  (MaximumListChunks.chunk_at 8 MaximumCall598StructuredFrom616From618Context.leaves).
Lemma values_eq :
  List.map MaximumCall598StructuredFrom616From618Context.depth
    (MaximumListChunks.chunk_at 8 MaximumCall598StructuredFrom616From618Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
