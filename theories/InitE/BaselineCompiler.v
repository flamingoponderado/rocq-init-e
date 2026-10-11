(** Concrete original compiler configuration and authoritative AST input.
    This definition uses no text parser and is not yet a bytecode certificate. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.cakeml.compiler Require compiler.
From Galette.cakeml.compiler.backend Require backend.
From Galette.cakeml.compiler.backend.riscv Require riscv_config.
From Galette.cakeml.pancake.proofs Require pan_to_targetProof.
From InitE.InitE Require Import SourceDeclarations MachineInitialization.
Open Scope N_scope.
Definition baselineBackendConfig : backend.config :=
 compiler.pancake_backend_conf riscv_config.riscv_backend_config.
Definition compilationMachine := challengeMachineConfig (n2w 0)
 (fun _ => False) (fun _ => False) [] 0 [].
Definition baselineCompilation :=
 pan_to_targetProof.compile_prog_max baselineBackendConfig compilationMachine sourceDeclarations.
