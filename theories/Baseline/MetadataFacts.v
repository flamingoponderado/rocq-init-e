(** Arithmetic and finite metadata obligations for the original baseline.
    No compiler-output equality, concrete ROM binding or certificate assumed. *)
From Galette Require Import Base.
From Stdlib Require Import List NArith Lia.
From Galette.HOL.src.n_bit Require Import words alignment.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.cakeml.compiler.backend Require lab_to_target.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From InitE.InitE Require Import Parameters MachineInitialization SubmissionModel.
From InitE.Baseline Require Import Metadata.
Open Scope N_scope.

Theorem baseline_metadata_lengths :
 LENGTH baselineNames = 17 /\ LENGTH baselineMmio = 15 /\
 LENGTH baselineEntryPcs = 17 /\ LENGTH baselineNames = baselineFirst+LENGTH baselineMmio.
Proof. repeat split; reflexivity. Qed.

Theorem baseline_name_boundary : ffiNameBoundaryValid baselineNames baselineFirst.
Proof.
 unfold ffiNameBoundaryValid; split; [vm_compute; congruence|].
 intros i Hi; change (i < 17) in Hi.
 assert (Hcases : In i (COUNT_LIST 17)) by (vm_compute; lia).
 vm_compute in Hcases.
 repeat destruct Hcases as [Hcases|Hcases]; try contradiction;
 subst i; vm_compute; congruence.
Qed.

Theorem baseline_mmio_valid : forall i, i < LENGTH baselineNames -> baselineFirst <= i ->
 mmioRecordValid (n2w baselineNativePc) baselineFirst baselineMmio i = true.
Proof.
 intros i Hi Hfirst; change (i < 17) in Hi; change (2 <= i) in Hfirst.
 assert (Hcases : In i (COUNT_LIST 17)) by (vm_compute; lia).
 vm_compute in Hcases.
 repeat destruct Hcases as [Hcases|Hcases]; try contradiction;
 subst i; try lia; vm_compute; reflexivity.
Qed.

Theorem baseline_entry_distinct : NoDup baselineEntryPcs.
Proof. apply ALL_DISTINCT_NoDup_list; vm_compute; reflexivity. Qed.

Theorem baseline_entry_loaded : forall a, In a baselineEntryPcs ->
 initialPc < w2n a /\ w2n a < initialPc+baselineRomLength.
Proof.
 assert (H : forallb (fun a : word 64 =>
  (initialPc <? w2n a) && (w2n a <? initialPc+baselineRomLength)) baselineEntryPcs = true)
  by (vm_compute; reflexivity).
 rewrite forallb_forall in H; intros a Ha; specialize (H a Ha).
 apply andb_true_iff in H as [H1 H2]; apply N.ltb_lt in H1; apply N.ltb_lt in H2; auto.
Qed.

Theorem baseline_entry_aligned : forall a, In a baselineEntryPcs -> aligned 2 a = true.
Proof.
 assert (H : forallb (aligned 2) baselineEntryPcs = true) by (vm_compute; reflexivity).
 rewrite forallb_forall in H; exact H.
Qed.

Theorem baseline_entry_dispatch_separate : forall a, In a baselineEntryPcs ->
 a <> baselineDispatchAddress 0 /\ a <> baselineDispatchAddress 1.
Proof.
 assert (H : forallb (fun a => negb (bool_decide (a = baselineDispatchAddress 0)) &&
  negb (bool_decide (a = baselineDispatchAddress 1))) baselineEntryPcs = true)
  by (vm_compute; reflexivity).
 rewrite forallb_forall in H; intros a Ha; specialize (H a Ha).
 apply andb_true_iff in H as [H0 H1]; split; intros E; subst a;
 rewrite (proj2 (bool_decide_spec _) eq_refl) in *; discriminate.
Qed.

Definition baselineProgramDomain (a : word 64) : Prop :=
 submissionMemoryDomain a /\ forall i, i < baselineFirst+2 -> a <> baselineDispatchAddress i.

Theorem baseline_mmio_program : forall rec, In rec baselineMmio ->
 baselineProgramDomain (n2w baselineNativePc+n2w (lab_to_target.entry_pc rec))%w.
Proof.
 assert (H : forallb (fun rec =>
  let a : word 64 := (n2w baselineNativePc+n2w (lab_to_target.entry_pc rec))%w in
  (initialPc <=? w2n a) && (w2n a <? initialPc+codeSizeLimit) &&
  negb (w2n a <? inputEnd) && (w2n a <? outputStart) &&
  (baselineNativePc <? w2n a)) baselineMmio = true) by (vm_compute; reflexivity).
 rewrite forallb_forall in H; intros rec Hin; specialize (H rec Hin).
 cbn zeta in H; repeat rewrite andb_true_iff in H.
 destruct H as [[[[Hlo Hhi] Hinp] Hout] Habove].
 apply N.leb_le in Hlo; apply N.ltb_lt in Hhi; apply N.ltb_lt in Hout; apply N.ltb_lt in Habove.
 apply Bool.negb_true_iff in Hinp; apply N.ltb_ge in Hinp.
 unfold baselineProgramDomain, submissionMemoryDomain, submissionSharedDomain.
 split.
 - split; [left; auto|]. unfold inputStart, outputStart in *; intros [[Ha Hb]|[Ha Hb]]; lia.
 - intros i Hi E.
   assert (Hcases : In i (COUNT_LIST 4)) by (change (i < 4) in Hi; vm_compute; lia).
   assert (Hd : w2n (baselineDispatchAddress i) < baselineNativePc).
   { vm_compute in Hcases; repeat destruct Hcases as [Hcases|Hcases]; try contradiction;
     subst i; vm_compute; congruence. }
   rewrite E in Habove; lia.
Qed.

Theorem baseline_exit_loaded : forall rec, In rec baselineMmio ->
 baselineNativePc+lab_to_target.exit_pc rec < initialPc+baselineRomLength.
Proof.
 assert (H : forallb (fun rec => baselineNativePc+lab_to_target.exit_pc rec <?
  initialPc+baselineRomLength) baselineMmio = true) by (vm_compute; reflexivity).
 rewrite forallb_forall in H; intros rec Hin; apply N.ltb_lt; exact (H rec Hin).
Qed.

Theorem baseline_numeric_admission :
 0 < baselineRomLength /\ baselineRomLength <= codeSizeLimit /\
 initialPc+lab_to_target.ffi_offset*(baselineFirst+2) < baselineNativePc /\
 baselineNativePc < initialPc+baselineRomLength /\
 aligned 2 (n2w baselineNativePc : word 64) = true /\
 baselineRomLength+lab_to_target.ffi_offset*(baselineFirst+3) < 2^64.
Proof. repeat split; vm_compute; congruence. Qed.

Theorem baseline_ordinary_slots_loaded : forall i, i < baselineFirst+2 ->
 initialPc < w2n (baselineDispatchAddress i) /\
 w2n (baselineDispatchAddress i) < initialPc+baselineRomLength.
Proof.
 intros i Hi; change (i < 4) in Hi.
 assert (Hcases : In i (COUNT_LIST 4)) by (vm_compute; lia).
 vm_compute in Hcases; repeat destruct Hcases as [Hcases|Hcases]; try contradiction;
 subst i; split; vm_compute; congruence.
Qed.

Theorem baseline_entry_config pcProgram shared :
 ffi_entry_pcs (challengeMachineConfig (n2w baselineNativePc) pcProgram shared
  baselineNames baselineFirst baselineMmio) = baselineEntryPcs.
Proof. reflexivity. Qed.

Theorem baseline_ordinary_entry_index : forall i, i < baselineFirst ->
 find_index (n2w baselineNativePc-n2w ((3+i)*lab_to_target.ffi_offset))%w
  baselineEntryPcs 0 = Some i.
Proof.
 intros i Hi; change (i < 2) in Hi.
 assert (Hcases : In i (COUNT_LIST 2)) by (vm_compute; lia).
 vm_compute in Hcases; repeat destruct Hcases as [Hcases|Hcases]; try contradiction;
 subst i; vm_compute; reflexivity.
Qed.

Theorem baseline_configuration_metadata program shared :
 let mc := challengeMachineConfig (n2w baselineNativePc) program shared
  baselineNames baselineFirst baselineMmio in
 ffi_names mc = baselineNames /\
 LENGTH (ffi_entry_pcs mc) = 17 /\
 NoDup (ffi_entry_pcs mc) /\
 (forall a, In a (ffi_entry_pcs mc) -> aligned 2 a = true) /\
 (forall a, In a (ffi_entry_pcs mc) ->
  a <> halt_pc mc /\ a <> ccache_pc mc).
Proof.
 cbn zeta; change (baselineNames = baselineNames /\ LENGTH baselineEntryPcs = 17 /\
 NoDup baselineEntryPcs /\ (forall a, In a baselineEntryPcs -> aligned 2 a = true) /\
 (forall a, In a baselineEntryPcs ->
 a <> baselineDispatchAddress 0 /\ a <> baselineDispatchAddress 1)).
 split; [reflexivity|]; split; [reflexivity|].
 split; [exact baseline_entry_distinct|].
 split; [exact baseline_entry_aligned|exact baseline_entry_dispatch_separate].
Qed.

Theorem baseline_submission_program s :
 anchorPc s = baselineNativePc -> first s = baselineFirst ->
 forall a, programDomain s a <-> baselineProgramDomain a.
Proof.
 intros Hpc Hfirst a; unfold programDomain, baselineProgramDomain, baselineDispatchAddress.
 rewrite Hpc, Hfirst; split; intros [Hdom Hslots]; split; [exact Hdom| |exact Hdom|];
 intros i Hi; specialize (Hslots i Hi).
 - replace ((1+i)*lab_to_target.ffi_offset) with (lab_to_target.ffi_offset*(i+1)) by nia.
   exact Hslots.
 - replace (lab_to_target.ffi_offset*(i+1)) with ((1+i)*lab_to_target.ffi_offset) by nia.
   exact Hslots.
Qed.

Theorem baseline_submission_entries s :
 anchorPc s = baselineNativePc -> names s = baselineNames ->
 first s = baselineFirst -> extra s = baselineMmio ->
 ffi_entry_pcs (machineConfig s) = baselineEntryPcs.
Proof. intros Hpc Hnames Hfirst Hextra; unfold machineConfig;
 rewrite Hpc, Hnames, Hfirst, Hextra; reflexivity. Qed.

Theorem baseline_submission_mmio_program s :
 anchorPc s = baselineNativePc -> first s = baselineFirst -> extra s = baselineMmio ->
 forall rec, In rec (extra s) ->
 programDomain s (n2w (anchorPc s)+n2w (lab_to_target.entry_pc rec))%w.
Proof.
 intros Hpc Hfirst Hextra rec Hin.
 rewrite (baseline_submission_program s Hpc Hfirst), Hpc.
 apply baseline_mmio_program; rewrite <- Hextra; exact Hin.
Qed.
