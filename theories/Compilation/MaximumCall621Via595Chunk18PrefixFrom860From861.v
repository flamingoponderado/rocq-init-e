From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall621Via595ContextFrom860From861.

Definition values := Eval vm_compute in
  List.map MaximumCall621Via595ContextFrom860From861.depth
    (List.firstn 4 (MaximumListChunks.chunk_at 18 MaximumCall621Via595ContextFrom860From861.leaves)).
Lemma values_eq :
  List.map MaximumCall621Via595ContextFrom860From861.depth
    (List.firstn 4 (MaximumListChunks.chunk_at 18 MaximumCall621Via595ContextFrom860From861.leaves)) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
