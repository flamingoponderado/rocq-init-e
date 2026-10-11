(** Fixed register initialization obligations for the original machine configuration. *)
From Galette Require Import Base.
From Galette.cakeml.compiler.backend.proofs Require backendProof.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require init_defs.
From Galette.cakeml.compiler.encoders.asm Require asmProps.
From InitE.Target Require Import TargetProperties.
From InitE.InitE Require Import BaselineCompiler MachineInitialization.
Theorem baseline_machine_initialization pc program shared names first extra :
 backendProof.mc_init_ok (asmProps.config Configuration.riscvTarget)
 baselineBackendConfig (challengeMachineConfig pc program shared names first extra).
Proof. unfold backendProof.mc_init_ok; repeat split; try reflexivity; vm_compute; intuition congruence. Qed.

Theorem machine_config_from_encoder pc program shared names first extra :
 asmProps.encoder_correct Configuration.riscvTarget ->
 init_defs.mc_conf_ok (challengeMachineConfig pc program shared names first extra).
Proof.
 intros He; unfold init_defs.mc_conf_ok.
 split; [vm_compute; auto|].
 split; [exact He|].
 do 5 (split; [vm_compute; reflexivity|]).
 exact (proj1 reduced_target_ok).
Qed.
