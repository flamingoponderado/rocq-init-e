(** Full original native compiler installation at the actual reached target state. *)
From Galette Require Import Base.
From Stdlib Require Import NArith Lia.
From Galette.HOL.src.n_bit Require Import words byte alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.cakeml.compiler.backend Require Import backend_common wordLang lab_to_target.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From Galette.cakeml.compiler.encoders.asm Require Import asmSem asmProps.
From Galette.cakeml.pancake.proofs Require Import pan_to_targetProof crep_to_loopProof.
From Galette.cakeml.misc Require Import misc.
From InitE.Guest Require Import Basic Bookkeeping.
From InitE.Target Require Import ReducedTypes Configuration.
From InitE.InitE Require Import Parameters BaselineArtifactLayout SubmissionModel SourceSemantics MachineInterference.
From InitE.Baseline Require Import Artifacts ArtifactFacts Submission Metadata MetadataFacts BootstrapMemory BootstrapCopyChecked BootstrapInstalledMemory PackedWordMemory HeaderInstallation BitmapSeparation SourceMemoryInstallation InstallationDomains GoodInitState BootstrapInitialRelation.
Open Scope N_scope.
Local Opaque bootstrapEndpoint nativeCode bitmaps installedMemory packedWordMemory baselineBitmapByteDomain.
Lemma numeric_heap_stack_domain :
 (fun a : word 64 => word_ls (n2w sourceBase) a /\ word_lo a (n2w ramEnd)) = baselineHeapStackDomain.
Proof.
 apply set_ext; intro a; change (is_true (word_ls (n2w sourceBase : word 64) a) /\ is_true (word_lo a (n2w ramEnd)) <-> baselineHeapStackDomain a).
 rewrite WORD_LS,WORD_LO; unfold baselineHeapStackDomain; change (sourceBase <= w2n a /\ w2n a < ramEnd <-> sourceBase <= w2n a /\ w2n a < ramEnd); reflexivity.
Qed.
Lemma endpoint_heap_stack_domain :
 (fun a : word 64 => word_ls (regs bootstrapEndpoint 11) a /\ word_lo a (regs bootstrapEndpoint 13)) = baselineHeapStackDomain.
Proof.
 destruct bootstrap_endpoint_heap_registers as [H10 [H11 [H12 H13]]].
 rewrite H11,H13; apply set_ext; intro a; change
 (is_true (word_ls (n2w sourceBase : word 64) a) /\ is_true (word_lo a (n2w ramEnd)) <-> baselineHeapStackDomain a).
 rewrite WORD_LS,WORD_LO; unfold baselineHeapStackDomain; change (sourceBase <= w2n a /\ w2n a < ramEnd <-> sourceBase <= w2n a /\ w2n a < ramEnd); reflexivity.
Qed.
Theorem baseline_pan_installed ms : target_state_rel riscvTarget bootstrapEndpoint ms ->
 pan_installed nativeCode 620 bitmaps 0 (Some baselineNames) (11,13)
 (machineConfig baselineSubmission) baselineMmio ms
 (fun a => crep_to_loopProof.wlab_wloc (sourceMemory a)) ordinaryDomain sharedDomain.
Proof.
 intro Hrelated.
 destruct bootstrap_endpoint_heap_registers as [H10 [H11 [H12 H13]]].
 pose proof Hrelated as [_ [Hpc _]]; rewrite bootstrap_endpoint_pc in Hpc.
 unfold pan_installed; cbn beta iota zeta.
 exists bootstrapEndpoint,(packedWordMemory installedMemory),(n2w (initDataRam+24)),baselineBitmapByteDomain,submissionSharedDomain.
 cbn beta iota zeta.
 split; [intros ad Had; apply installed_ordinary_word; exact Had|].
 split.
 - rewrite endpoint_heap_stack_domain; exact (baseline_good_init_state ms Hrelated).
 - split; [exact baseline_source_shared_domain|].
   rewrite H11,H13.
   split; [vm_compute; reflexivity|].
   split; [vm_compute; reflexivity|].
   split; [vm_compute; reflexivity|].
   split; [vm_compute; reflexivity|].
   split; [vm_compute; reflexivity|].
   split.
   + rewrite numeric_heap_stack_domain; exact baseline_bitmap_heap_stack_disjoint.
   + split.
     * exact (installed_source_header_word 0 ltac:(lia)).
     * split.
       -- rewrite baseline_bitmap_end_address.
          change (packedWordMemory installedMemory (n2w (sourceBase+8*1)) = wordLang.Word (nthN 1 startupHeaders (n2w 0))).
          exact (installed_source_header_word 1 ltac:(lia)).
       -- split.
          ++ pose proof (proj1 (proj2 original_literal_sizes)) as Hbits.
             rewrite Hbits; change
              (packedWordMemory installedMemory (n2w (sourceBase+8*2)) = wordLang.Word (nthN 2 startupHeaders (n2w 0))).
             exact (installed_source_header_word 2 ltac:(lia)).
          ++ split.
             ** change (packedWordMemory installedMemory (n2w sourceBase+n2w 3*bytes_in_word)%w = wordLang.Word (get_pc riscvTarget ms+n2w (LENGTH nativeCode))%w).
                rewrite Hpc,(proj1 original_literal_sizes).
                change (packedWordMemory installedMemory (n2w (sourceBase+8*3)) = wordLang.Word (nthN 3 startupHeaders (n2w 0))).
                exact (installed_source_header_word 3 ltac:(lia)).
             ** split.
                --- change (packedWordMemory installedMemory (n2w sourceBase+n2w 4*bytes_in_word)%w = wordLang.Word (get_pc riscvTarget ms+n2w 620+n2w (LENGTH nativeCode))%w).
                    rewrite Hpc,(proj1 original_literal_sizes).
                    change (packedWordMemory installedMemory (n2w (sourceBase+8*4)) = wordLang.Word (nthN 4 startupHeaders (n2w 0))).
                    exact (installed_source_header_word 4 ltac:(lia)).
                --- split; [exact baseline_bitmap_installed_separation|].
                    split; [reflexivity|].
                    intros i Hi; change (mmio_pcs_min_index baselineNames = Some i) in Hi.
                    rewrite baseline_mmio_min_index in Hi; injection Hi as <-.
                    rewrite baseline_machine_target,Hpc; split.
                    +++ vm_compute; reflexivity.
                    +++ split.
                        *** lazy; reflexivity.
                        *** rewrite (proj1 original_literal_sizes); vm_compute; congruence.
Qed.
Theorem baseline_pan_installed_input input ms : target_state_rel riscvTarget bootstrapEndpoint ms ->
 pan_installed nativeCode 620 bitmaps 0 (Some baselineNames) (11,13)
 (machineConfig baselineSubmission) baselineMmio ms
 (fun a => crep_to_loopProof.wlab_wloc (Galette.cakeml.pancake.semantics.panSem.memory (sourceInitialState input) a))
 (Galette.cakeml.pancake.semantics.panSem.memaddrs (sourceInitialState input))
 (Galette.cakeml.pancake.semantics.panSem.sh_memaddrs (sourceInitialState input)).
Proof. exact (baseline_pan_installed ms). Qed.
