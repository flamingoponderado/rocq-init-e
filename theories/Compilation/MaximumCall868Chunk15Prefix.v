From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks MaximumCall868SuffixContext.

Definition values := Eval vm_compute in
  List.map MaximumCall868SuffixContext.depth
    (List.firstn 0 (MaximumListChunks.chunk_at 15 MaximumCall868SuffixContext.leaves)).
Lemma values_eq :
  List.map MaximumCall868SuffixContext.depth
    (List.firstn 0 (MaximumListChunks.chunk_at 15 MaximumCall868SuffixContext.leaves)) = values.
Proof. vm_cast_no_check (eq_refl values). Qed.
