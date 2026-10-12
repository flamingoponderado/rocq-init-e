(** Original concrete machine configuration, with encoder obligations closed. *)
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require init_defs.
From InitE.Target Require Import ReducedEncoderCases.
From InitE.InitE Require Import MachineInitialization MachineConfigFacts.
Theorem challenge_machine_configuration pc program shared names first extra :
 init_defs.mc_conf_ok (challengeMachineConfig pc program shared names first extra).
Proof. apply machine_config_from_encoder; exact reduced_riscv_encoder_correct. Qed.
