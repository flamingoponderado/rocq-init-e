(** Materialized lower-backend checkpoints for the exact compiler. *)
From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require backend word_to_stack word_depth
 bvl_to_bvi stack_to_lab stack_rawcall stack_alloc stack_remove stack_names
 data_to_word backend_common lab_to_target.
From InitE.InitE Require Import BaselineCompiler NativeCompilation.
From InitE.Compilation Require Import CompilerConfig.
Open Scope N_scope.
From InitE.Compilation Require WordPipeline Stack RawCalls StackAllocation.
Definition removed := Eval vm_compute in stack_remove.compile (stack_to_lab.jump (backend.stack_conf baselineBackendConfig))
 (asm.addr_offset ac)
 (stack_to_lab.is_gen_gc (data_to_word.gc_kind (backend.data_conf baselineBackendConfig)))
 (2 * data_to_word.max_heap_limit 64 (backend.data_conf baselineBackendConfig) - 1)
 (asm.reg_count ac - (list.LENGTH (asm.avoid_regs ac) + 3))
 bvl_to_bvi.InitGlobals_location StackAllocation.allocated.
Lemma removed_eq : stack_remove.compile (stack_to_lab.jump (backend.stack_conf baselineBackendConfig))
 (asm.addr_offset ac)
 (stack_to_lab.is_gen_gc (data_to_word.gc_kind (backend.data_conf baselineBackendConfig)))
 (2 * data_to_word.max_heap_limit 64 (backend.data_conf baselineBackendConfig) - 1)
 (asm.reg_count ac - (list.LENGTH (asm.avoid_regs ac) + 3))
 bvl_to_bvi.InitGlobals_location StackAllocation.allocated = removed.
Proof. vm_cast_no_check (eq_refl removed). Qed.
