From Galette Require Import Base.
From Stdlib Require Import List.
From Galette.cakeml.compiler.backend Require Import wordLang.
From InitE.Compilation Require Import MaximumCall602Via606Context.

Definition value := Eval vm_compute in MaximumCall602Via606Context.depth
  (List.nth 6 MaximumCall602Via606Context.leaves wordLang.Skip).
Lemma value_eq : MaximumCall602Via606Context.depth
  (List.nth 6 MaximumCall602Via606Context.leaves wordLang.Skip) = value.
Proof. vm_cast_no_check (eq_refl value). Qed.
