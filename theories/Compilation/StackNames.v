(** Materialized lower-backend checkpoints for the exact compiler. *)
From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require backend word_to_stack word_depth
 bvl_to_bvi stack_to_lab stack_rawcall stack_alloc stack_remove stack_names
 data_to_word backend_common lab_to_target.
From InitE.InitE Require Import BaselineCompiler NativeCompilation.
From InitE.Compilation Require Import CompilerConfig.
Open Scope N_scope.
From InitE.Compilation Require WordPipeline Stack RawCalls StackAllocation StackRemoval.
Definition renamed := Eval vm_compute in stack_names.compile (stack_to_lab.reg_names (backend.stack_conf baselineBackendConfig)) StackRemoval.removed.
Lemma renamed_eq : stack_names.compile (stack_to_lab.reg_names (backend.stack_conf baselineBackendConfig)) StackRemoval.removed = renamed.
Proof. vm_cast_no_check (eq_refl renamed). Qed.
