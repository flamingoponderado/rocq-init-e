From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall603Via616From618Context.

Definition values := Eval vm_compute in
  List.map MaximumCall603Via616From618Context.depth
    (List.firstn 5 (MaximumListChunks.chunk_at 7 MaximumCall603Via616From618Context.leaves)).
Lemma values_eq :
  List.map MaximumCall603Via616From618Context.depth
    (List.firstn 5 (MaximumListChunks.chunk_at 7 MaximumCall603Via616From618Context.leaves)) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
