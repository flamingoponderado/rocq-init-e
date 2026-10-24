From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall619Via623ContextFrom860From861.

Definition values := Eval vm_compute in
  List.map MaximumCall619Via623ContextFrom860From861.depth
    (List.skipn 3 (MaximumListChunks.chunk_at 5 MaximumCall619Via623ContextFrom860From861.leaves)).
Lemma values_eq :
  List.map MaximumCall619Via623ContextFrom860From861.depth
    (List.skipn 3 (MaximumListChunks.chunk_at 5 MaximumCall619Via623ContextFrom860From861.leaves)) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
