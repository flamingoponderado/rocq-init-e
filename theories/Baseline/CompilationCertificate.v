(** Concrete original bytes/bitmaps plus returned dispatch metadata.
    This is the real compilation equality, not a count or hash diagnostic. *)
From Galette Require Import Base.
From Galette.cakeml.compiler.backend Require Import backend.
From Galette.cakeml.compiler.backend Require lab_to_target.
From InitE.InitE Require Import BaselineCompiler NativeCompilation.
From InitE.Baseline Require Import Artifacts Metadata.
From InitE.Compilation Require ConcreteCertificate.
Open Scope N_scope.
Theorem concrete_compilation : exists configuration : backend.config,
 baselineCompilation = (Some (nativeCode,(bitmaps,configuration)),Some 538) /\
 lab_to_target.ffi_names (backend.lab_conf configuration) = Some baselineNames /\
 lab_to_target.shmem_extra (backend.lab_conf configuration) = baselineMmio.
Proof. exact ConcreteCertificate.concrete_compilation. Qed.
Print Assumptions concrete_compilation.
