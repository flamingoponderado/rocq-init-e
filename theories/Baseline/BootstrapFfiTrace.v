(** Actual finite bootstrap trace with FFI guards at every executed edge. *)
From Galette Require Import Base.
From Stdlib Require Import NArith Lia.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.relation Require Import relation.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem targetProps.
From Galette.cakeml.semantics.ffi Require Import ffi.
From InitE.Guest Require Import Basic.
From InitE.InitE Require Import Parameters SubmissionModel BaselineArtifactLayout.
From InitE.Target Require Import ReducedTypes Configuration.
From InitE.Baseline Require Import Metadata Submission SubmissionFacts BootstrapMemory BootstrapProgram BootstrapPrefix BootstrapSteps BootstrapCopyLoop BootstrapCopyInvariant BootstrapCopyChecked BootstrapCodeFacts BootstrapTail BootstrapEvaluator BootstrapInitialRelation BootstrapComposition.
Open Scope N_scope.
Definition BootstrapRange (s : asm_state 64) (i : asm.asm 64) : Prop :=
 initialPc <= w2n (pc s) /\
 w2n (pc s)+LENGTH (riscv_target.riscv_enc i) <= initialPc+208.
Lemma bootstrap_ffi_entry_bound x : In x (ffi_entry_pcs (machineConfig baselineSubmission)) ->
 initialPc+208 <= w2n x.
Proof.
 rewrite baselineSubmission_entry_pcs; intro Hin.
 vm_compute in Hin; repeat destruct Hin as [Hin|Hin]; try contradiction;
 subst x; vm_compute; congruence.
Qed.
Theorem bootstrap_range_ffi s i : BootstrapRange s i ->
 ffi_entry_pcs_disjoint (machineConfig baselineSubmission) s (LENGTH (riscv_target.riscv_enc i)).
Proof.
 intros [Hlo Hhi]; unfold ffi_entry_pcs_disjoint; apply DISJOINT_iff.
 intros x [Hentry [offset [E Hoff]]].
 apply IN_set in Hentry.
 pose proof (bootstrap_ffi_entry_bound x Hentry) as HentryBound.
 apply (f_equal w2n) in E.
 assert (Hoffset : w2n (n2w offset : word 64) = offset).
 { rewrite w2n_n2w; change (dimword 64) with (2^64); apply N.mod_small; unfold initialPc in *; lia. }
 unfold word_add in E; rewrite Hoffset,w2n_n2w in E.
 change (dimword 64) with (2^64) in E.
 rewrite N.mod_small in E by (unfold initialPc in *; lia).
 unfold initialPc in *; lia.
Qed.
Local Opaque after copyState copyIteration.
Fixpoint SafeCode instructions (s : asm_state 64) : Prop :=
 match instructions with
 | [] => True
 | i::rest => BootstrapRange s i /\ SafeCode rest (after s i)
 end.
Theorem safe_checked_trace instructions s : Checked instructions s -> SafeCode instructions s ->
 RTC (EvaluatorStep (machineConfig baselineSubmission)) s (runCode instructions s).
Proof.
 revert s; induction instructions as [|i rest IH]; intros s Hchecked Hsafe; cbn [runCode].
 - apply rtc_refl.
 - destruct Hchecked as [Hstep Hchecked]; destruct Hsafe as [Hrange Hsafe].
   eapply rtc_step.
   + exists i; split; [exact Hstep|]. split.
     * apply bootstrap_range_ffi; exact Hrange.
     * apply tail_after_mem_domain.
   + apply IH; assumption.
Qed.
Theorem prefix_safe_code s : pc s = n2w initialPc -> SafeCode prefixCode s.
Proof.
 intro Hp.
 change (SafeCode [bootLoc 5 0x80000000 initDataRom; bootLoc 6 0x80000008 initDataRam; bootLoc 7 0x80000010 initDataEnd] s).
 unfold bootLoc; cbn [SafeCode BootstrapRange].
 repeat apply conj.
 all: tail_pc_regs.
 all: try rewrite Hp.
 all: vm_compute; (congruence || exact I).
Qed.
Theorem copy_safe_code k s : k < 4617 -> CopyControl k s -> SafeCode copyLoopCode s.
Proof.
 intros Hk [H5 H6 H7 Hb Hd Hl Ha Hf Hp].
 assert (Ek : (k <? 4617) = true) by (apply N.ltb_lt; exact Hk); rewrite Ek in Hp.
 cbn [copyLoopCode SafeCode BootstrapRange].
 repeat apply conj.
 all: copy_check_pc.
 all: try rewrite Hp.
 all: vm_compute; (congruence || exact I).
Qed.
Theorem tail_safe_code s : pc s = n2w 0x8000002c -> SafeCode tailCode s.
Proof.
 intro Hp; rewrite tail_code_list; cbn [tailInstructions SafeCode bootLoc bootConst bootShift bootStore BootstrapRange].
 repeat apply conj.
 all: tail_pc_regs.
 all: try rewrite Hp.
 all: vm_compute; (congruence || exact I).
Qed.
Theorem copy_guarded_loop_trace k : k <= 4617 ->
 RTC (EvaluatorStep (machineConfig baselineSubmission)) copyEntryAsm (copyState k).
Proof.
 induction k using N.peano_ind; intro Hk.
 - rewrite copy_state_zero; apply rtc_refl.
 - eapply RTC_RTC with (y:=copyState k); [apply IHk; lia|].
   rewrite copy_state_successor,copy_iteration_run; apply safe_checked_trace.
   + apply copy_body_state_checked; lia.
   + apply copy_safe_code with (k:=k); [lia|apply copy_control_all; lia].
Qed.
Theorem full_bootstrap_guarded_trace :
 RTC (EvaluatorStep (machineConfig baselineSubmission)) initialAsm bootstrapEndpoint.
Proof.
 eapply RTC_RTC with (y:=copyEntryAsm).
 - rewrite <- prefix_endpoint; apply safe_checked_trace.
   + exact prefix_checked.
   + apply prefix_safe_code; reflexivity.
 - eapply RTC_RTC with (y:=copyState 4617).
   + apply copy_guarded_loop_trace; lia.
   + unfold bootstrapEndpoint; apply safe_checked_trace.
     * apply tail_checked.
       -- exact (copy_pc 4617 (copyState 4617) (copy_control_all 4617 ltac:(lia))).
       -- exact (copy_endian 4617 (copyState 4617) (copy_control_all 4617 ltac:(lia))).
       -- exact (copy_domain 4617 (copyState 4617) (copy_control_all 4617 ltac:(lia))).
       -- exact (copy_link 4617 (copyState 4617) (copy_control_all 4617 ltac:(lia))).
       -- exact (copy_alignment 4617 (copyState 4617) (copy_control_all 4617 ltac:(lia))).
       -- exact (copy_failed 4617 (copyState 4617) (copy_control_all 4617 ltac:(lia))).
       -- apply copy_control_code with (k:=4617); [lia|apply copy_bytes_all; lia].
     * apply tail_safe_code; exact (copy_pc 4617 (copyState 4617) (copy_control_all 4617 ltac:(lia))).
Qed.
Theorem full_bootstrap_clock_shift {F} (input : InputBlob) (io : ffi_state F) :
 exists count ms2,
 ClockShift (machineConfig baselineSubmission) io count (initialState baselineSubmission input) ms2 /\
 target_state_rel riscvTarget bootstrapEndpoint ms2 /\
 prog_addresses (machineConfig baselineSubmission) = mem_domain bootstrapEndpoint.
Proof.
 apply rtc_evaluator with (before:=initialAsm).
 - exact baseline_machine_target.
 - exact baseline_machine_identity.
 - exact baseline_machine_domain.
 - exact full_bootstrap_guarded_trace.
 - exact (baseline_initial_relation input).
Qed.
