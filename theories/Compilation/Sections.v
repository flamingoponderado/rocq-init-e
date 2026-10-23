(** Materialized lower-backend checkpoints for the exact compiler. *)
From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require backend word_to_stack word_depth
 bvl_to_bvi stack_to_lab stack_rawcall stack_alloc stack_remove stack_names
 data_to_word backend_common lab_to_target.
From InitE.InitE Require Import BaselineCompiler NativeCompilation.
From InitE.Compilation Require Import CompilerConfig.
Open Scope N_scope.
From InitE.Compilation Require WordPipeline Stack RawCalls StackAllocation StackRemoval StackNames.
Definition sections := Eval vm_compute in list.MAP stack_to_lab.prog_to_section StackNames.renamed.
Lemma sections_eq : list.MAP stack_to_lab.prog_to_section StackNames.renamed = sections.
Proof. vm_cast_no_check (eq_refl sections). Qed.
