From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.coretypes Require Import option.
From InitE.Compilation Require Import MaximumContext.
Open Scope N_scope.

Lemma root_lookup :
  sptree.lookup MaximumContext.root MaximumContext.funs =
  Some (fst (THE (sptree.lookup MaximumContext.root MaximumContext.funs)),
    MaximumContext.program).
Proof. vm_cast_no_check
  (eq_refl (sptree.lookup MaximumContext.root MaximumContext.funs)). Qed.

