(** Materialized lower-backend checkpoints for the exact compiler. *)
From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.cakeml.compiler.backend Require backend word_to_stack word_depth
 bvl_to_bvi stack_to_lab stack_rawcall stack_alloc stack_remove stack_names
 data_to_word backend_common lab_to_target.
From InitE.InitE Require Import BaselineCompiler NativeCompilation.
From InitE.Compilation Require Import CompilerConfig MaximumRootFullValue.
Open Scope N_scope.
From InitE.Compilation Require Pipeline Frontend WordPipeline Stack RawCalls StackAllocation StackRemoval StackNames Sections Target.
Definition maximum := MaximumRootFullValue.maximum.
Lemma maximum_eq : word_depth.max_depth (word_to_stack.stack_frame_size (fst (snd Stack.stackResult)))
 (word_depth.full_call_graph bvl_to_bvi.InitGlobals_location (sptree.fromAList WordPipeline.optimized)) = maximum.
Proof. exact MaximumRootFullValue.maximum_eq. Qed.
