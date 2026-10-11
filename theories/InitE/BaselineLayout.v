(** Fixed numeric installation layout from the original init-e baseline.
    These facts do not prove native-byte installation or a stack certificate. *)
From Galette Require Import Base.
From Galette.cakeml.compiler.backend Require backend data_to_word stack_remove.
From InitE.InitE Require Import Parameters BaselineCompiler.
Open Scope N_scope.
Definition baselineHeapLen : N := (stackStart-sourceBase)/8.
Definition baselineAdj2 : N := sourceBase+8*stack_remove.max_stack_alloc.
Definition baselineAdj4 : N := ramEnd-8*stack_remove.max_stack_alloc.
Theorem baseline_numeric_layout :
 0 < sourceBase /\ sourceBase < stackStart /\
 globalsWords <= baselineHeapLen /\
 sourceBase+8*baselineHeapLen-globalsWords*8 = heapEnd /\
 (stackStart-sourceBase) mod 16 = 0 /\
 baselineAdj2 <= stackStart /\ stackStart <= baselineAdj4 /\
 stackStart-sourceBase <= 8*(2*data_to_word.max_heap_limit 64 (backend.data_conf baselineBackendConfig)-1) /\
 8*(2*data_to_word.max_heap_limit 64 (backend.data_conf baselineBackendConfig)-1) < 2^64.
Proof. repeat split; vm_compute; congruence. Qed.
Theorem baseline_heap_region :
 sourceBase+8*baselineHeapLen = stackStart /\
 baselineHeapLen*8+globalsWords*8 <= ramSize /\ ramEnd < 2^64.
Proof. repeat split; vm_compute; congruence. Qed.
