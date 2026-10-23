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
Definition simplified := Eval vm_compute in pan_simp.compile_prog sourceDeclarations.
Lemma simplified_eq : pan_simp.compile_prog sourceDeclarations = simplified.
Proof. vm_cast_no_check (eq_refl simplified). Qed.
Definition structured := Eval vm_compute in pan_structs.compile_top simplified.
Lemma structured_eq : pan_structs.compile_top simplified = structured.
Proof. vm_cast_no_check (eq_refl structured). Qed.
Definition globals := Eval vm_compute in pan_globals.compile_top structured (strlit "main").
Lemma globals_eq : pan_globals.compile_top structured (strlit "main") = globals.
Proof. vm_cast_no_check (eq_refl globals). Qed.
Definition crep := Eval vm_compute in pan_to_crep.compile_prog globals.
Lemma crep_eq : pan_to_crep.compile_prog globals = crep.
Proof. vm_cast_no_check (eq_refl crep). Qed.
Definition loops := Eval vm_compute in crep_to_loop.compile_prog
 (asm.ISA riscv_target.riscv_config) crep.
Lemma loops_eq : crep_to_loop.compile_prog (asm.ISA riscv_target.riscv_config) crep = loops.
Proof. vm_cast_no_check (eq_refl loops). Qed.
Definition words := Eval vm_compute in loop_to_word.compile loops.
Lemma words_eq : loop_to_word.compile loops = words.
Proof. vm_cast_no_check (eq_refl words). Qed.
Theorem frontend_eq : pan_to_word.compile_prog (asm.ISA riscv_target.riscv_config)
 sourceDeclarations = words.
Proof.
 unfold pan_to_word.compile_prog.
 rewrite simplified_eq, structured_eq, globals_eq, crep_eq, loops_eq, words_eq.
 reflexivity.
Qed.
