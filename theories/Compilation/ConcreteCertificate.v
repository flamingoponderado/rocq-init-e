(** Concrete original bytes/bitmaps plus returned dispatch metadata.
    This is the real compilation equality, not a count or hash diagnostic. *)
From Galette Require Import Base.
From Galette.cakeml.compiler.backend Require Import backend.
From Galette.cakeml.compiler.backend Require lab_to_target.
From InitE.InitE Require Import BaselineCompiler NativeCompilation.
From InitE.Baseline Require Import Artifacts Metadata.
From InitE.Compilation Require Complete.
Open Scope N_scope.
(** The compiler has already been evaluated in small, independently checked
    checkpoints. Selecting the returned configuration does not rerun it. *)
Definition checkedConfiguration : backend.config := Eval vm_compute in
 match fst Complete.result with
 | Some (_,(_,configuration)) => configuration
 | None => baselineBackendConfig
 end.
Lemma checked_result : Complete.result =
 (Some (nativeCode,(bitmaps,checkedConfiguration)),Some 538).
Proof. vm_cast_no_check (eq_refl Complete.result). Qed.

Theorem concrete_compilation : exists configuration : backend.config,
 baselineCompilation = (Some (nativeCode,(bitmaps,configuration)),Some 538) /\
 lab_to_target.ffi_names (backend.lab_conf configuration) = Some baselineNames /\
 lab_to_target.shmem_extra (backend.lab_conf configuration) = baselineMmio.
Proof.
 exists checkedConfiguration. split.
 - rewrite Complete.staged_compilation_eq. exact checked_result.
 - split.
   + vm_cast_no_check (eq_refl
       (lab_to_target.ffi_names (backend.lab_conf checkedConfiguration))).
   + vm_cast_no_check (eq_refl
       (lab_to_target.shmem_extra (backend.lab_conf checkedConfiguration))).
Qed.
Print Assumptions concrete_compilation.
