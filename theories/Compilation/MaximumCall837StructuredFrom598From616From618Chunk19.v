From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall837StructuredFrom598From616From618Context.

Definition values := Eval vm_compute in List.map MaximumCall837StructuredFrom598From616From618Context.depth
  (MaximumListChunks.chunk_at 19 MaximumCall837StructuredFrom598From616From618Context.leaves).
Lemma values_eq :
  List.map MaximumCall837StructuredFrom598From616From618Context.depth
    (MaximumListChunks.chunk_at 19 MaximumCall837StructuredFrom598From616From618Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
