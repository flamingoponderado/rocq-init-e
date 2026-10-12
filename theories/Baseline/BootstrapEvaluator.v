(** FFI-aware lifting of finite bootstrap assembly execution.
    Original BootstrapSteps/BootstrapComposition interfaces: the machine state
    at the endpoint is constructed by the evaluator bridge, never assumed. *)
From Galette Require Import Base.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.relation Require Import relation.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem targetProps.
From Galette.cakeml.semantics.ffi Require Import ffi.
From InitE.Target Require Import ReducedTypes Configuration.
From InitE.Baseline Require Import BootstrapSteps BootstrapComposition.
Open Scope N_scope.

Definition AssemblyStep (before post : asm_state 64) : Prop :=
 exists i, asm_step riscv_target.riscv_config before i post.

(** The caller supplies the actual FFI exclusion and memory-domain frame for
    every edge of the finite trace. In particular, exclusion only at the start
    of the bootstrap is insufficient for this interface. *)
Definition EvaluatorStep (mc : machine_config 64 riscv_state RiscVProjection)
 (before post : asm_state 64) : Prop :=
 exists i, asm_step riscv_target.riscv_config before i post /\
 ffi_entry_pcs_disjoint mc before (LENGTH (riscv_target.riscv_enc i)) /\
 mem_domain post = mem_domain before.

Lemma assembly_step_after before post i :
 asm_step riscv_target.riscv_config before i post -> post = after before i.
Proof.
 intros (_ & _ & _ & _ & Hpost & _); symmetry; exact Hpost.
Qed.
Lemma identity_interference_ok {S Q : Type} (projection : S -> Q) :
 interference_ok (fun _ state => state) projection.
Proof. intros count state; reflexivity. Qed.

Theorem evaluator_step {F : Type}
 (mc : machine_config 64 riscv_state RiscVProjection) (io : ffi_state F)
 before post ms :
 target mc = riscvTarget -> next_interfer mc = (fun _ state => state) ->
 prog_addresses mc = mem_domain before -> EvaluatorStep mc before post ->
 target_state_rel riscvTarget before ms ->
 exists count ms2, ClockShift mc io count ms ms2 /\
 target_state_rel riscvTarget post ms2 /\ count <> 0 /\
 prog_addresses mc = mem_domain post.
Proof.
 intros Htarget Hidentity Hdomain [i [Hstep [Hdisjoint Hframe]]] Hrelated.
 pose proof (assembly_step_after before post i Hstep) as Hpost; subst post.
 destruct (step_evaluator mc before ms io i Htarget Hdomain Hdisjoint)
  as [count [ms2 [Hshift [Hrel Hpositive]]]].
 - rewrite Hidentity; apply identity_interference_ok.
 - exact Hstep.
 - exact Hrelated.
 - exists count,ms2; apply conj.
   + intros k; rewrite (Hshift k),identity_interference_shift by exact Hidentity; reflexivity.
   + apply conj; [exact Hrel|]. apply conj; [exact Hpositive|]. rewrite Hframe; exact Hdomain.
Qed.

(** Reflexive traces use zero clocks. Each actual assembly edge contributes
    the positive clock count supplied by [BootstrapSteps.step_evaluator]. *)
Theorem rtc_evaluator {F : Type}
 (mc : machine_config 64 riscv_state RiscVProjection) (io : ffi_state F)
 before final ms :
 target mc = riscvTarget -> next_interfer mc = (fun _ state => state) ->
 prog_addresses mc = mem_domain before ->
 RTC (EvaluatorStep mc) before final -> target_state_rel riscvTarget before ms ->
 exists count ms2, ClockShift mc io count ms ms2 /\
 target_state_rel riscvTarget final ms2 /\ prog_addresses mc = mem_domain final.
Proof.
 intros Htarget Hidentity Hdomain Htrace.
 revert ms Hdomain; induction Htrace as [state|first middle last Hedge Htail IH];
  intros ms Hdomain Hrelated.
 - exists 0,ms; apply conj; [apply clock_shift_reflexive|]. split; assumption.
 - destruct (evaluator_step mc io first middle ms Htarget Hidentity Hdomain Hedge Hrelated)
    as [n [middleMs [Hfirst [Hmiddle [_ HmiddleDomain]]]]].
   destruct (IH middleMs HmiddleDomain Hmiddle) as [m [finalMs [Hrest [Hfinal HfinalDomain]]]].
   exists (m+n),finalMs; apply conj.
   + eapply clock_shift_compose; eassumption.
   + split; assumption.
Qed.

(** A nonempty trace has a positive evaluator shift, even when assembly
    instructions expand to several target instructions. *)
Theorem edge_rtc_evaluator {F : Type}
 (mc : machine_config 64 riscv_state RiscVProjection) (io : ffi_state F)
 before middle final ms :
 target mc = riscvTarget -> next_interfer mc = (fun _ state => state) ->
 prog_addresses mc = mem_domain before -> EvaluatorStep mc before middle ->
 RTC (EvaluatorStep mc) middle final -> target_state_rel riscvTarget before ms ->
 exists count ms2, ClockShift mc io count ms ms2 /\
 target_state_rel riscvTarget final ms2 /\ count <> 0 /\
 prog_addresses mc = mem_domain final.
Proof.
 intros Htarget Hidentity Hdomain Hedge Htail Hrelated.
 destruct (evaluator_step mc io before middle ms Htarget Hidentity Hdomain Hedge Hrelated)
  as [n [middleMs [Hfirst [Hmiddle [Hpositive HmiddleDomain]]]]].
 destruct (rtc_evaluator mc io middle final middleMs Htarget Hidentity HmiddleDomain Htail Hmiddle)
  as [m [finalMs [Hrest [Hfinal HfinalDomain]]]].
 exists (m+n),finalMs; apply conj.
 - eapply clock_shift_compose; eassumption.
 - apply conj; [exact Hfinal|]. split; [lia|exact HfinalDomain].
Qed.

(** This alternative accepts an ordinary assembly RTC proof. Its guard
    hypothesis covers actual intermediate edges lying on a path from the
    supplied start to the supplied endpoint, rather than arbitrary machine PCs. *)
Theorem guard_assembly_trace mc before final : RTC AssemblyStep before final ->
 (forall state post i, RTC AssemblyStep before state ->
  asm_step riscv_target.riscv_config state i post -> RTC AssemblyStep post final ->
  ffi_entry_pcs_disjoint mc state (LENGTH (riscv_target.riscv_enc i)) /\
  mem_domain post = mem_domain state) ->
 RTC (EvaluatorStep mc) before final.
Proof.
 intro Htrace; induction Htrace as [state|first middle last Hedge Htail IH]; intro Hguards.
 - apply rtc_refl.
 - destruct Hedge as [i Hstep]; eapply rtc_step.
   + exists i; apply conj; [exact Hstep|]. apply Hguards.
     * apply rtc_refl.
     * exact Hstep.
     * exact Htail.
   + apply IH; intros state post instruction Hprefix Hstep2 Hsuffix.
     apply (Hguards state post instruction).
     * eapply rtc_step; [exists i; exact Hstep|exact Hprefix].
     * exact Hstep2.
     * exact Hsuffix.
Qed.
Theorem assembly_rtc_evaluator {F : Type}
 (mc : machine_config 64 riscv_state RiscVProjection) (io : ffi_state F)
 before final ms :
 target mc = riscvTarget -> next_interfer mc = (fun _ state => state) ->
 prog_addresses mc = mem_domain before -> RTC AssemblyStep before final ->
 (forall state post i, RTC AssemblyStep before state ->
  asm_step riscv_target.riscv_config state i post -> RTC AssemblyStep post final ->
  ffi_entry_pcs_disjoint mc state (LENGTH (riscv_target.riscv_enc i)) /\
  mem_domain post = mem_domain state) ->
 target_state_rel riscvTarget before ms ->
 exists count ms2, ClockShift mc io count ms ms2 /\
 target_state_rel riscvTarget final ms2 /\ prog_addresses mc = mem_domain final.
Proof.
 intros Htarget Hidentity Hdomain Htrace Hguards Hrelated; apply rtc_evaluator with (before:=before);
 try assumption; apply guard_assembly_trace; assumption.
Qed.

(** The clock equation retains the FFI state and hence the terminating output
    and events, exactly as the original composition interface requires. *)
Theorem evaluator_trace_termination {F : Type}
 (mc : machine_config 64 riscv_state RiscVProjection) (io : ffi_state F)
 before final ms out events :
 target mc = riscvTarget -> next_interfer mc = (fun _ state => state) ->
 prog_addresses mc = mem_domain before -> RTC (EvaluatorStep mc) before final ->
 target_state_rel riscvTarget before ms ->
 (forall ms2, target_state_rel riscvTarget final ms2 ->
  machine_sem mc io ms2 (Terminate out events)) ->
 machine_sem mc io ms (Terminate out events).
Proof.
 intros Htarget Hidentity Hdomain Htrace Hrelated Hpost.
 destruct (rtc_evaluator mc io before final ms Htarget Hidentity Hdomain Htrace Hrelated)
  as [count [ms2 [Hshift [Hrel _]]]].
 eapply termination_from_clock_shift; [exact Hshift|apply Hpost; exact Hrel].
Qed.
