From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall595StructuredContextFrom860From861.

Definition values := Eval vm_compute in List.map MaximumCall595StructuredContextFrom860From861.depth
  (MaximumListChunks.chunk_at 114 MaximumCall595StructuredContextFrom860From861.leaves).
Lemma values_eq :
  List.map MaximumCall595StructuredContextFrom860From861.depth
    (MaximumListChunks.chunk_at 114 MaximumCall595StructuredContextFrom860From861.leaves) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
