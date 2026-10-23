(** Materialized compiler checkpoints.  Each equality is opaque, so downstream
    proofs rewrite it rather than evaluating the source compiler again. *)
From Galette Require Import Base.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.pancake Require pan_simp pan_structs pan_globals pan_to_crep
 crep_to_loop loop_to_word pan_to_word.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From Galette.cakeml.basis.pure Require Import mlstring.
From InitE.InitE Require Import SourceDeclarations.
Open Scope N_scope.
Open Scope hol_string_scope.
From InitE.Compilation Require Import FrontendSimplify FrontendStructs FrontendGlobals.
Definition crep := Eval vm_compute in pan_to_crep.compile_prog globals.
Lemma crep_eq : pan_to_crep.compile_prog globals = crep.
Proof. vm_cast_no_check (eq_refl crep). Qed.
