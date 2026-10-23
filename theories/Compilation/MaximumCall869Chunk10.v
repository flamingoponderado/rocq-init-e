From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall869Context MaximumCall869Pieces.

Definition values := Eval vm_compute in List.map MaximumCall869Context.depth (MaximumListChunks.chunk_at 10 MaximumCall869Pieces.suffix).
Lemma values_eq : List.map MaximumCall869Context.depth (MaximumListChunks.chunk_at 10 MaximumCall869Pieces.suffix) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
