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
From InitE.Compilation Require Export FrontendSimplify FrontendStructs FrontendGlobals FrontendCrep FrontendLoops FrontendWords.
Definition words := FrontendWords.words.
Theorem frontend_eq : pan_to_word.compile_prog (asm.ISA riscv_target.riscv_config)
 sourceDeclarations = words.
Proof.
 unfold pan_to_word.compile_prog.
 rewrite simplified_eq, structured_eq, globals_eq, crep_eq, loops_eq, words_eq.
 reflexivity.
Qed.
