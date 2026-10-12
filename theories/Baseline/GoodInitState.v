(** Every actually reached related target state satisfies native good_init_state. *)
From Galette Require Import Base.
From Stdlib Require Import Lia.
From Galette.HOL.src.n_bit Require Import words byte.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.encoders.asm Require Import asmSem asmProps.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import inst.
From InitE.Target Require Import ReducedTypes Configuration.
From InitE.InitE Require Import Parameters SubmissionModel MachineInterference.
From InitE.Baseline Require Import Artifacts Submission BootstrapMemory BootstrapCopyChecked BootstrapInstalledMemory BootstrapEvaluator BootstrapInitialRelation PackedWordMemory NativeCodeInstallation InstallationDomains NativeStart.
Open Scope N_scope.
Local Opaque bootstrapEndpoint nativeCode installedMemory packedWordMemory baselineDataDomain.
Theorem endpoint_native_bytes_in_mem :
 bytes_in_mem (pc bootstrapEndpoint) nativeCode (mem bootstrapEndpoint) (mem_domain bootstrapEndpoint) baselineDataDomain.
Proof.
 rewrite bootstrap_endpoint_pc,(proj1 bootstrap_endpoint_controls).
 apply bytes_in_mem_literal; intros j Hj; split.
 - apply native_byte_domain; exact Hj.
 - split.
   + apply native_byte_data_excluded; rewrite native_literal_length in Hj; lia.
   + apply endpoint_native_byte; exact Hj.
Qed.
Theorem baseline_good_init_state ms : target_state_rel riscvTarget bootstrapEndpoint ms ->
 good_init_state (machineConfig baselineSubmission) ms nativeCode 620 bootstrapEndpoint
 (packedWordMemory installedMemory) baselineDataDomain submissionSharedDomain.
Proof.
 intro Hrelated; pose proof Hrelated as [_ [Hpc _]].
 destruct bootstrap_endpoint_controls as [Hd [Hl [Ha [Hb Hf]]]].
 unfold good_init_state; split; [exact Hrelated|].
 split; [exact endpoint_target_configured|].
 split; [symmetry; exact Hpc|].
 split; [exact endpoint_start_pc|].
 split.
 - rewrite Ha,bootstrap_endpoint_pc; vm_compute; reflexivity.
 - split.
   + rewrite baseline_machine_identity; apply identity_interference_ok.
   + split.
     * rewrite bootstrap_endpoint_pc; exact baseline_machine_ffiOk.
     * split.
       -- rewrite bootstrap_endpoint_pc; exact baseline_machine_cacheOk.
       -- split; [apply endpoint_native_code_loaded; exact Hrelated|].
          split; [exact endpoint_native_bytes_in_mem|].
          split.
          ++ rewrite Hd; exact baseline_data_domain_subset.
          ++ split.
             ** intros ad Had; apply baseline_data_domain_closed; exact Had.
             ** split; [reflexivity|]. split.
                --- intros ad Had; apply baseline_shared_domain_closed; exact Had.
                --- split; [exact baseline_program_shared_disjoint|]. split.
                    +++ intros ad; rewrite bootstrap_endpoint_memory.
                        exact (packedWordMemory_certificate installedMemory ad).
                    +++ split.
                        *** intros n Hn; rewrite bootstrap_endpoint_pc,Hd; apply baseline_code_buffer; exact Hn.
                        *** exact baseline_code_size_bound.
Qed.
