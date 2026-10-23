(** Materialized lower-backend checkpoints for the exact compiler. *)
From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require backend word_to_stack word_depth
 bvl_to_bvi stack_to_lab stack_rawcall stack_alloc stack_remove stack_names
 data_to_word backend_common lab_to_target.
From InitE.InitE Require Import BaselineCompiler NativeCompilation.
From InitE.Compilation Require Import CompilerConfig.
Open Scope N_scope.
From InitE.Compilation Require Pipeline Frontend WordPipeline Stack RawCalls StackAllocation StackRemoval StackNames Sections Target.
From InitE.Compilation Require Import Maximum.
Definition result :=
 (backend.attach_bitmaps sptree.LN baselineBackendConfig (fst Stack.stackResult) Target.targetResult, maximum).
Local Opaque compileWithConfig.
Theorem staged_compilation_eq : baselineCompilation = result.
Proof.
 rewrite <- direct_compilation_exact.
 unfold directCompilation, result.
 eapply Pipeline.compile_with_checkpoints with
 (words := Frontend.words) (optimized := WordPipeline.optimized)
 (wc := fst (snd Stack.stackResult))
 (fs := fst (snd (snd Stack.stackResult)))
 (stack := snd (snd (snd Stack.stackResult)))
 (raw := RawCalls.rawCalls) (allocated := StackAllocation.allocated)
 (removed := StackRemoval.removed) (renamed := StackNames.renamed)
 (sections := Sections.sections).
 - exact Frontend.frontend_eq.
 - exact WordPipeline.word_pipeline_eq.
 - exact Stack.stackResult_eq.
 - exact RawCalls.rawCalls_eq.
 - exact StackAllocation.allocated_eq.
 - exact StackRemoval.removed_eq.
 - exact StackNames.renamed_eq.
 - exact Sections.sections_eq.
 - exact Target.targetResult_eq.
 - exact maximum_eq.
Qed.
