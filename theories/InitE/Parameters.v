(** Original InitE/Parameters.lean; all arithmetic uses unbounded N. *)
From Stdlib Require Import NArith Lia.
Open Scope N_scope.
Definition initialPc : N := 2147483648.
Definition codeSizeLimit : N := 134217728.
Definition inputStart : N := 1073741824.
Definition inputSize : N := 134217728.
Definition inputEnd : N := inputStart + inputSize.
Definition outputStart : N := 2688614400.
Definition outputSize : N := 65536.
Definition outputEnd : N := outputStart + outputSize.
Definition ramStart : N := 2684354560.
Definition ramSize : N := 29 * 1024 * 1024 * 1024.
Definition ramEnd : N := ramStart + ramSize.
Definition sourceBase : N := 2701131776.
(** The guest's frame/scratch arena starts at its allocation ceiling
    0xb0000000, inside the compiler's source-memory domain. *)
Definition scratchStart : N := 2952790016.
Definition scratchEnd : N := 2965299200.
Definition heapStart : N := sourceBase.
Definition stackSize : N := 16 * 1024 * 1024.
Definition stackStart : N := ramEnd - stackSize.
Definition globalsWords : N := 67.
Definition heapEnd : N := stackStart - globalsWords * 8.
Definition gasLimit : N := 200000000.
Theorem regions_disjoint :
 inputEnd <= initialPc /\ initialPc + codeSizeLimit <= ramStart /\
 ramStart <= outputStart /\ outputEnd <= heapStart /\ heapStart < scratchStart /\
 scratchStart < scratchEnd /\ scratchEnd <= heapEnd /\
 heapEnd + globalsWords * 8 = stackStart /\ stackStart < ramEnd.
Proof. repeat split; vm_compute; congruence. Qed.
Theorem ramEnd_aligned : ramEnd mod 4096 = 0.
Proof. vm_compute; reflexivity. Qed.
Theorem heapEnd_aligned : heapEnd mod 8 = 0.
Proof. vm_compute; reflexivity. Qed.
Theorem baseline_stack_room : 7480 * 8 < stackSize.
Proof. vm_compute; reflexivity. Qed.
