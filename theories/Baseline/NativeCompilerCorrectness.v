(** Correctness of the actual baseline native entry, reusing Galette's full
    compiler theorem. Compilation and installation are intermediate lemmas
    to be discharged by the concrete certificate, never challenge premises. *)
From Galette Require Import Base Classical.
From Stdlib Require Import NArith Lia.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.string Require Import string.
From Galette.HOL.src.finite_maps Require Import finite_map.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.semantics.proofs Require Import semanticsProps.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.backend Require Import backend backend_common stack_remove stack_to_lab lab_to_target data_to_word.
From Galette.cakeml.compiler.backend.proofs Require Import backendProof stack_removeProof.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From Galette.cakeml.pancake Require Import panLang pan_globals.
From Galette.cakeml.pancake.semantics Require panSem.
From Galette.cakeml.pancake.proofs Require Import pan_to_targetProof.
From Galette.cakeml.pancake.proofs Require crep_to_loopProof.
From InitE.Guest Require Import Basic GasLimit.
From InitE.Target Require Import ReducedTypes Configuration.
From InitE.InitE Require Import Parameters BaselineArtifactLayout BaselineCompiler BaselineLayout
 NativeCompilation SourceDeclarations SourceSemantics SourceFacts SourceOrder SourceAllocation
 BackendConfigFacts MachineConfigFacts MachineConfigCorrect MachineInitialization SubmissionModel
 TargetTotality.
From InitE.Baseline Require Import Artifacts Metadata Submission SubmissionFacts BootstrapCopyChecked
 BootstrapInstalledMemory NativeEntryResources.
Open Scope N_scope.
Open Scope hol_string_scope.
Local Opaque Artifacts.code nativeCode bitmaps baselineCompilation bootstrapEndpoint sourceMemory sourceBehaviour.

(** The compiler consults only the target assembly configuration. This proof
    never evaluates the closed original compiler input. *)
Theorem native_compile_config_congruence {B C D E} c
 (left : machine_config 64 B C) (right : machine_config 64 D E) declarations :
 asmProps.config (target left) = asmProps.config (target right) ->
 compile_prog_max c left declarations = compile_prog_max c right declarations.
Proof. intro H; rewrite !compile_with_config_exact,H; reflexivity. Qed.
Local Transparent baselineCompilation.
Theorem baseline_compile_at_machine cprime :
 baselineCompilation = (Some (nativeCode,(bitmaps,cprime)),Some 538) ->
 compile_prog_max baselineBackendConfig (machineConfig baselineSubmission) sourceDeclarations =
 (Some (nativeCode,(bitmaps,cprime)),Some 538).
Proof.
 intro H; rewrite <- H; unfold baselineCompilation.
 apply native_compile_config_congruence; reflexivity.
Qed.
Local Opaque baselineCompilation.
Theorem native_entry_registers ms : target_state_rel riscvTarget bootstrapEndpoint ms ->
 get_reg riscvTarget ms 11 = n2w sourceBase /\
 get_reg riscvTarget ms 12 = n2w stackStart /\ get_reg riscvTarget ms 13 = n2w ramEnd.
Proof.
 intros [_ [_ [_ [Hr _]]]].
 destruct bootstrap_endpoint_heap_registers as [_ [H11 [H12 H13]]].
 split; [rewrite Hr by (vm_compute; intuition congruence); exact H11|].
 split; [rewrite Hr by (vm_compute; intuition congruence); exact H12|].
 rewrite Hr by (vm_compute; intuition congruence); exact H13.
Qed.

Lemma native_machine_target : target (machineConfig baselineSubmission) = riscvTarget.
Proof. reflexivity. Qed.

(** Exactly the source-memory, ordinary-domain and shared-domain arguments
    of Galette's [pan_installed], at the original fixed registers and metadata. *)
Definition baseline_native_pan_installed (ms : riscv_state) : Prop :=
 pan_installed nativeCode 620 bitmaps 0 (Some baselineNames) (11,13)
  (machineConfig baselineSubmission) baselineMmio ms
  (fun a => crep_to_loopProof.wlab_wloc (sourceMemory a)) ordinaryDomain sharedDomain.

Definition native_precision (ms : riscv_state) : bool :=
 @bool_decide (option_lt (Some 538) (Some (fst (read_limits (asmProps.config riscvTarget)
  baselineBackendConfig (machineConfig baselineSubmission) ms)))) (Classical.classical_decision _).

Theorem native_baseline_correct input ms cprime :
 baselineCompilation = (Some (nativeCode,(bitmaps,cprime)),Some 538) ->
 lab_to_target.ffi_names (backend.lab_conf cprime) = Some baselineNames ->
 lab_to_target.shmem_extra (backend.lab_conf cprime) = baselineMmio ->
 target_state_rel riscvTarget bootstrapEndpoint ms ->
 baseline_native_pan_installed ms -> sourceBehaviour input <> Fail ->
 forall behaviour, machine_sem (machineConfig baselineSubmission) (sourceFfi input) ms behaviour ->
 behaviour = sourceBehaviour input.
Proof.
 intros Hcomp Hnames Hmmio Hrelated Hinstalled Hnonfail.
 pose proof (baseline_compile_at_machine cprime Hcomp) as Hcompile.
 destruct (native_entry_registers ms Hrelated) as [H11 [H12 H13]].
 assert (Hlimits : read_limits (asmProps.config riscvTarget) baselineBackendConfig (machineConfig baselineSubmission) ms =
   (2097104,1944059904)) by (apply baseline_read_limits; assumption).
 assert (Hsem : machine_sem (machineConfig baselineSubmission) (sourceFfi input) ms SUBSET
  extend_with_resource_limit'
   (native_precision ms)
   (fun b => b = sourceBehaviour input)).
 { rewrite <- source_declarations_behaviour.
   unfold native_precision.
   apply (pan_to_target_compile_semantics baselineBackendConfig (machineConfig baselineSubmission)
    sourceDeclarations nativeCode bitmaps cprime (Some 538) (sourceInitialState input) ms
    globalsWords baselineHeapLen (n2w baselineAdj2) (n2w baselineAdj4) (sourceFfi input) 620 0 (strlit "main")).
   apply conj; [exact Hcompile|].
   apply conj; [exact source_good_panops|].
   apply conj; [exact source_distinct_parameters|].
   apply conj; [exact source_distinct_names|].
   apply conj; [reflexivity|].
   apply conj; [reflexivity|].
   apply conj; [reflexivity|].
   apply conj; [exact source_exception_bound|].
   apply conj; [reflexivity|].
   apply conj; [exact baseline_backend_configuration|].
   apply conj; [rewrite baselineSubmission_machine_config; apply challenge_machine_configuration|].
   apply conj; [rewrite baselineSubmission_machine_config; apply baseline_machine_initialization|].
   apply conj; [discriminate|].
   apply conj.
   { change (word_lo (n2w 0) (get_reg riscvTarget ms 11)).
     rewrite H11; vm_compute; congruence. }
   apply conj.
   { rewrite source_structs_empty; cbn [option.THE]; symmetry; exact source_globals_size. }
   apply conj.
   { change (word_lo (get_reg riscvTarget ms 11) (get_reg riscvTarget ms 12)).
     rewrite H11,H12; vm_compute; congruence. }
   apply conj; [exact H11|].
   apply conj; [apply source_globals_allocatable|].
   apply conj.
   { change (baselineHeapLen = w2n (get_reg riscvTarget ms 12 + word_2comp (n2w 1) * n2w sourceBase)%w / 8).
     rewrite H12; vm_compute; reflexivity. }
   apply conj.
   { apply (proj1 (w2n_11 _ _)); vm_compute; reflexivity. }
   apply conj; [exact (proj1 (proj2 (proj2 baseline_numeric_layout)))|].
   apply conj.
   { change (ordinaryDomain = addresses (get_reg riscvTarget ms 11) (baselineHeapLen-globalsWords)).
     rewrite H11; reflexivity. }
   apply conj.
   { change (aligned 4 (get_reg riscvTarget ms 12 + word_2comp (n2w 1)*get_reg riscvTarget ms 11)%w = true).
     rewrite H11,H12; vm_compute; reflexivity. }
   apply conj.
   { change (n2w baselineAdj2 = (get_reg riscvTarget ms 11 + bytes_in_word*n2w max_stack_alloc)%w).
     rewrite H11; apply (proj1 (w2n_11 _ _)); vm_compute; reflexivity. }
   apply conj.
   { change (n2w baselineAdj4 = (get_reg riscvTarget ms 13 - bytes_in_word*n2w max_stack_alloc)%w).
     rewrite H13; apply (proj1 (w2n_11 _ _)); vm_compute; reflexivity. }
   apply conj.
   { change (word_ls (n2w baselineAdj2) (get_reg riscvTarget ms 12)).
     rewrite H12; vm_compute; congruence. }
   apply conj.
   { change (word_ls (get_reg riscvTarget ms 12) (n2w baselineAdj4)).
     rewrite H12; vm_compute; congruence. }
   apply conj.
   { change (w2n (get_reg riscvTarget ms 12+word_2comp (n2w 1)*get_reg riscvTarget ms 11)%w <=
      8*(2*max_heap_limit 64 (backend.data_conf baselineBackendConfig)-1)).
     rewrite H11,H12; vm_compute; congruence. }
   apply conj; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 baseline_numeric_layout))))))))|].
   apply conj; [reflexivity|].
   apply conj; [reflexivity|].
   apply conj; [reflexivity|].
   apply conj; [rewrite Hnames,Hmmio; exact Hinstalled|].
   apply conj; [reflexivity|].
   rewrite source_declarations_behaviour; exact Hnonfail.
 }
 unfold native_precision in Hsem; rewrite Hlimits in Hsem.
 assert (Hprecise : @bool_decide (option_lt (Some 538) (Some (fst (2097104,1944059904)))) (Classical.classical_decision _) = true).
 { apply (proj2 (bool_decide_spec _)); vm_compute; reflexivity. }
 rewrite Hprecise in Hsem; exact Hsem.
Qed.

(** Target totality prevents vacuous correctness and supplies the exact
    terminating behaviour of the actual native evaluator. *)
Theorem native_baseline_terminates input ms cprime out events :
 baselineCompilation = (Some (nativeCode,(bitmaps,cprime)),Some 538) ->
 lab_to_target.ffi_names (backend.lab_conf cprime) = Some baselineNames ->
 lab_to_target.shmem_extra (backend.lab_conf cprime) = baselineMmio ->
 target_state_rel riscvTarget bootstrapEndpoint ms -> baseline_native_pan_installed ms ->
 sourceBehaviour input = Terminate out events ->
 machine_sem (machineConfig baselineSubmission) (sourceFfi input) ms (Terminate out events).
Proof.
 intros Hcomp Hnames Hmmio Hrelated Hinstalled Hsource.
 assert (Hnonfail : sourceBehaviour input <> Fail) by (rewrite Hsource; discriminate).
 pose proof (native_baseline_correct input ms cprime Hcomp Hnames Hmmio Hrelated Hinstalled Hnonfail) as Hcorrect.
 apply target_termination_of_behaviour_eq; intros b Hb.
 rewrite <- Hsource; exact (Hcorrect b Hb).
Qed.
Theorem native_baseline_finite_execution input ms cprime out events :
 baselineCompilation = (Some (nativeCode,(bitmaps,cprime)),Some 538) ->
 lab_to_target.ffi_names (backend.lab_conf cprime) = Some baselineNames ->
 lab_to_target.shmem_extra (backend.lab_conf cprime) = baselineMmio ->
 target_state_rel riscvTarget bootstrapEndpoint ms -> baseline_native_pan_installed ms ->
 sourceBehaviour input = Terminate out events ->
 exists steps post finalFfi,
 evaluate (machineConfig baselineSubmission) (sourceFfi input) steps ms = (Halt out,(post,finalFfi)) /\
 io_events finalFfi = events.
Proof.
 intros Hcomp Hnames Hmmio Hrelated Hinstalled Hsource.
 exact (native_baseline_terminates input ms cprime out events Hcomp Hnames Hmmio Hrelated Hinstalled Hsource).
Qed.
