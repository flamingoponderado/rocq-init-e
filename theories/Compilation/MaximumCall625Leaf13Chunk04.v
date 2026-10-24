From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall625Leaf13Context.

Definition values := Eval vm_compute in List.map MaximumCall625Leaf13Context.depth
  (MaximumListChunks.chunk_at 4 MaximumCall625Leaf13Context.leaves).
Lemma values_eq :
  List.map MaximumCall625Leaf13Context.depth
    (MaximumListChunks.chunk_at 4 MaximumCall625Leaf13Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
