(** Original native entry PC, reserved dispatch slots and machine configuration. *)
From Galette Require Import Base.
From Stdlib Require Import NArith Lia.
From Galette.HOL.src.n_bit Require Import words alignment.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.backend Require lab_to_target.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From Galette.cakeml.compiler.encoders.asm Require Import asmSem asmProps.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From InitE.InitE Require Import Parameters BaselineArtifactLayout SubmissionModel MachineInterference.
From InitE.Baseline Require Import Metadata MetadataFacts Submission BootstrapMemory BootstrapInstalledMemory BootstrapCopyChecked.
Open Scope N_scope.
Local Opaque bootstrapEndpoint.
Theorem baseline_dispatch_not_program i : i < 4 -> ~ bootstrapDomain (baselineDispatchAddress i).
Proof.
 intros Hi [_ Hslots]; apply (Hslots i Hi).
 unfold baselineDispatchAddress; change ((n2w nativePc-n2w ((1+i)*16) : word 64)%w = (n2w nativePc-n2w (16*(i+1)))%w).
 replace ((1+i)*16) with (16*(i+1)) by lia; reflexivity.
Qed.
Theorem baseline_dispatch_not_shared i : i < 4 -> ~ submissionSharedDomain (baselineDispatchAddress i).
Proof.
 intro Hi; pose proof (baseline_ordinary_slots_loaded i Hi) as [Hlo Hhi].
 unfold submissionSharedDomain; cbv [initialPc baselineRomLength inputStart inputEnd inputSize outputStart outputEnd outputSize] in *.
 intros [[H1 H2]|[H1 H2]]; lia.
Qed.
Theorem baseline_start_pc_from_boundary (Hboundary : mmio_pcs_min_index baselineNames = Some 2) : start_pc_ok (machineConfig baselineSubmission) (n2w nativePc).
Proof.
 change (~ bootstrapDomain (baselineDispatchAddress 0) /\
 ~ bootstrapDomain (baselineDispatchAddress 1) /\
 ~ submissionSharedDomain (baselineDispatchAddress 0) /\
 ~ submissionSharedDomain (baselineDispatchAddress 1) /\
 (n2w nativePc-n2w 16 : word 64)%w = baselineDispatchAddress 0 /\
 (n2w nativePc-n2w 32 : word 64)%w = baselineDispatchAddress 1 /\
 (n2w 1 && n2w nativePc : word 64)%w = n2w 0 /\
 exists i, mmio_pcs_min_index baselineNames = Some i /\
 (forall index, index < i ->
 ~ bootstrapDomain (n2w nativePc-n2w ((3+index)*16))%w /\
 ~ submissionSharedDomain (n2w nativePc-n2w ((3+index)*16))%w /\
 (n2w nativePc-n2w ((3+index)*16))%w <> baselineDispatchAddress 0 /\
 (n2w nativePc-n2w ((3+index)*16))%w <> baselineDispatchAddress 1 /\
 misc.find_index (n2w nativePc-n2w ((3+index)*16))%w baselineEntryPcs 0 = Some index) /\
 (forall index, index < LENGTH baselineNames /\ i <= index ->
 baselineDispatchAddress 0 <> EL index baselineEntryPcs /\
 baselineDispatchAddress 1 <> EL index baselineEntryPcs) /\
 LENGTH baselineNames = LENGTH baselineEntryPcs).
 split; [apply baseline_dispatch_not_program; lia|].
 split; [apply baseline_dispatch_not_program; lia|].
 split; [apply baseline_dispatch_not_shared; lia|].
 split; [apply baseline_dispatch_not_shared; lia|].
 split; [reflexivity|]. split; [reflexivity|]. split; [vm_compute; reflexivity|].
 exists 2; split; [exact Hboundary|]. split.
 - intros index Hi.
   assert (E : (n2w nativePc-n2w ((3+index)*16) : word 64)%w = baselineDispatchAddress (index+2)).
   { unfold baselineDispatchAddress; replace (3+index) with (1+(index+2)) by lia; reflexivity. }
   split; [rewrite E; apply baseline_dispatch_not_program; lia|].
   split; [rewrite E; apply baseline_dispatch_not_shared; lia|].
   split.
   + intro He; apply (f_equal w2n) in He.
     assert (Hin : In index (COUNT_LIST 2)) by (vm_compute; lia).
     vm_compute in Hin; repeat destruct Hin as [Hin|Hin]; try contradiction; subst index; vm_compute in He; discriminate.
   + split.
     * intro He; apply (f_equal w2n) in He.
       assert (Hin : In index (COUNT_LIST 2)) by (vm_compute; lia).
       vm_compute in Hin; repeat destruct Hin as [Hin|Hin]; try contradiction; subst index; vm_compute in He; discriminate.
     * apply baseline_ordinary_entry_index; exact Hi.
 - split.
   + intros index [Hi Hfirst].
     change (index < 17) in Hi; assert (Hin : In index (COUNT_LIST 17)) by (vm_compute; lia).
     vm_compute in Hin; repeat destruct Hin as [Hin|Hin]; try contradiction; subst index; try lia; split; vm_compute; congruence.
   + reflexivity.
Qed.
Theorem endpoint_target_configured : target_configured bootstrapEndpoint (machineConfig baselineSubmission).
Proof.
 destruct bootstrap_endpoint_controls as [Hd [Hl [Ha [Hb Hf]]]].
 unfold target_configured; split; [rewrite Hf; discriminate|].
 split; [exact Hb|]. split; [exact Ha|]. split; [exact Hd|exact Hl].
Qed.
Theorem endpoint_start_pc_from_boundary (Hboundary : mmio_pcs_min_index baselineNames = Some 2) : start_pc_ok (machineConfig baselineSubmission) (pc bootstrapEndpoint).
Proof. rewrite bootstrap_endpoint_pc; exact (baseline_start_pc_from_boundary Hboundary). Qed.
Theorem endpoint_pc_mask : (n2w (2^align bootstrapEndpoint-1) && pc bootstrapEndpoint : word 64)%w = n2w 0.
Proof.
 rewrite (proj1 (proj2 (proj2 bootstrap_endpoint_controls))),bootstrap_endpoint_pc; vm_compute; reflexivity.
Qed.

Theorem baseline_start_pc : start_pc_ok (machineConfig baselineSubmission) (n2w nativePc).
Proof. apply baseline_start_pc_from_boundary; exact baseline_mmio_min_index. Qed.
Theorem endpoint_start_pc : start_pc_ok (machineConfig baselineSubmission) (pc bootstrapEndpoint).
Proof. apply endpoint_start_pc_from_boundary; exact baseline_mmio_min_index. Qed.
