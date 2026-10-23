(** Materialized lower-backend checkpoints for the exact compiler. *)
From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require backend word_to_stack word_depth
 bvl_to_bvi stack_to_lab stack_rawcall stack_alloc stack_remove stack_names
 data_to_word backend_common lab_to_target.
From InitE.InitE Require Import BaselineCompiler NativeCompilation.
From InitE.Compilation Require Import CompilerConfig.
Open Scope N_scope.
From InitE.Compilation Require WordPipeline.
Definition stackResult := Eval vm_compute in word_to_stack.compile ac false WordPipeline.optimized.
Lemma stackResult_eq : word_to_stack.compile ac false WordPipeline.optimized = stackResult.
Proof. vm_cast_no_check (eq_refl stackResult). Qed.
