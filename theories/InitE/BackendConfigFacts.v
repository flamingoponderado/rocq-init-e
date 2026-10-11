From Galette Require Import Base.
From Galette.cakeml.compiler.backend.proofs Require backendProof.
From Galette.cakeml.compiler.encoders.asm Require asmProps.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From InitE.Target Require Import RegisterNameFacts Configuration BackendBounds.
From InitE.InitE Require Import BaselineCompiler.
Theorem baseline_backend_configuration :
 backendProof.backend_config_ok (asmProps.config riscvTarget) baselineBackendConfig.
Proof.
 unfold backendProof.backend_config_ok.
 repeat match goal with |- _ /\ _ => split end.
 all: try reflexivity.
 all: try apply riscv_names_bijective.
 all: try apply riscv_names_admissible.
 - vm_compute; intuition congruence.
 - vm_compute; intuition congruence.
 - vm_compute; intuition congruence.
 - vm_compute; intuition congruence.
 - vm_compute; intuition congruence.
 - vm_compute; intuition congruence.
 - vm_compute; intuition congruence.
 - intros w [Hl Hu]; apply small_byte_offset; assumption.
 - intro name; apply (proj1 (stack_store_offset_bounds name)).
 - intro name; apply (proj2 (stack_store_offset_bounds name)).
 - intros n H; change (asm.valid_imm riscv_target.riscv_config (inl asm.Sub) (words.n2w (n*8)) /\ asm.valid_imm riscv_target.riscv_config (inl asm.Add) (words.n2w (n*8))).
   apply stack_allocation_immediate; exact H.
Qed.
