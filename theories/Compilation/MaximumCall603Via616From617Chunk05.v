From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall603Via616From617Context.

Definition values := Eval vm_compute in List.map MaximumCall603Via616From617Context.depth
  (MaximumListChunks.chunk_at 5 MaximumCall603Via616From617Context.leaves).
Lemma values_eq :
  List.map MaximumCall603Via616From617Context.depth
    (MaximumListChunks.chunk_at 5 MaximumCall603Via616From617Context.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
