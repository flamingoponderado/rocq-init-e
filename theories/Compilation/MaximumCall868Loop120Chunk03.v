From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall868Loop120Context.

Definition values := Eval vm_compute in List.map MaximumCall868Loop120Context.depth
  (MaximumListChunks.chunk_at 3 MaximumCall868Loop120Context.leaves).
Lemma values_eq :
  List.map MaximumCall868Loop120Context.depth
    (MaximumListChunks.chunk_at 3 MaximumCall868Loop120Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
