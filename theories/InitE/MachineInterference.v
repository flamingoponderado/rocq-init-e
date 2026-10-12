(** Original MachineInitialization interference contracts, over the exact
    reduced-machine callbacks and arbitrary returned byte lists. *)
From Galette Require Import Base.
From Stdlib Require Import List NArith Lia Bool.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.finite_maps Require Import alist.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.coretypes Require Import option.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.encoders.riscv Require Import riscv_target.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From InitE.Target Require Import ReducedTypes Configuration.
From InitE.InitE Require Import Parameters BaselineArtifactLayout MachineInitialization SubmissionModel.
From InitE.Baseline Require Import Metadata MetadataFacts Submission SubmissionFacts.
Open Scope N_scope.

Lemma machine_bool_false (P : Prop) `{Decision P} : ~ P -> bool_decide P = false.
Proof. intro Hn; destruct (bool_decide P) eqn:E; [apply bool_decide_spec in E; contradiction|reflexivity]. Qed.

Lemma machineSetPc_pc s pc :
 riscv_state_c_PC (machineSetPc s pc) (riscv_state_procID (machineSetPc s pc)) = pc.
Proof.
 change ((if bool_decide (riscv_state_procID s = riscv_state_procID s) then pc
  else riscv_state_c_PC s (riscv_state_procID s)) = pc).
 rewrite (proj2 (bool_decide_spec _) eq_refl); reflexivity.
Qed.
Lemma machineSetPc_reg s pc r :
 riscv_state_c_gpr (machineSetPc s pc) (riscv_state_procID (machineSetPc s pc)) r =
 riscv_state_c_gpr s (riscv_state_procID s) r.
Proof. reflexivity. Qed.
Lemma machineSetPc_memory s pc : riscv_state_MEM8 (machineSetPc s pc) = riscv_state_MEM8 s.
Proof. reflexivity. Qed.
Lemma machineSetReg_pc s reg value :
 riscv_state_c_PC (machineSetReg s reg value) (riscv_state_procID (machineSetReg s reg value)) =
 riscv_state_c_PC s (riscv_state_procID s).
Proof. reflexivity. Qed.
Lemma machineSetReg_memory s reg value : riscv_state_MEM8 (machineSetReg s reg value) = riscv_state_MEM8 s.
Proof. reflexivity. Qed.
Lemma machineSetReg_current s reg value :
 riscv_state_c_gpr (machineSetReg s reg value) (riscv_state_procID (machineSetReg s reg value)) (n2w reg) = value.
Proof.
 change ((if bool_decide (riscv_state_procID s = riscv_state_procID s) &&
 bool_decide ((n2w reg : word 5) = n2w reg) then value
 else riscv_state_c_gpr s (riscv_state_procID s) (n2w reg)) = value).
 rewrite !(proj2 (bool_decide_spec _) eq_refl); reflexivity.
Qed.
Lemma machineSetPc_ok s pc : riscvOk s = true -> aligned 2 pc = true -> riscvOk (machineSetPc s pc) = true.
Proof.
 intros Hs Hp; unfold riscvOk in *; apply andb_true_iff in Hs as [Hs _].
 cbv [machineSetPc riscv_state_c_PC_fupd riscv_state_c_MCSR riscv_state_c_NextFetch riscv_state_exception riscv_state_procID riscv_state_c_PC].
 rewrite (proj2 (bool_decide_spec _) eq_refl),Hp,andb_true_r; exact Hs.
Qed.
Lemma machineSetReg_ok s reg value : riscvOk (machineSetReg s reg value) = riscvOk s.
Proof. reflexivity. Qed.
Lemma machineMemory_ok s update : riscvOk (riscv_state_MEM8_fupd update s) = riscvOk s.
Proof. reflexivity. Qed.
Lemma machineCacheInterference_contract s k a b :
 riscv_state_MEM8 (machineCacheInterference k (a,(b,s))) = riscv_state_MEM8 s /\
 riscv_state_c_gpr (machineCacheInterference k (a,(b,s))) = riscv_state_c_gpr s /\
 riscv_state_c_PC (machineCacheInterference k (a,(b,s))) (riscv_state_procID s) =
 riscv_state_c_gpr s (riscv_state_procID s) (n2w 1).
Proof. split; [reflexivity|]; split; [reflexivity|]; apply machineSetPc_pc. Qed.

Lemma machineSetPc_relation s t pc : aligned 2 pc = true -> target_state_rel riscvTarget t s ->
 target_state_rel riscvTarget (set_pc pc t) (machineSetPc s pc).
Proof.
 intros Hp [Hok [_ [Hmem [Hregs Hfp]]]].
 apply conj; [apply machineSetPc_ok; assumption|].
 apply conj; [apply machineSetPc_pc|].
 apply conj; [exact Hmem|]. apply conj; [exact Hregs|].
 intros i Hi; change (i < 0) in Hi; lia.
Qed.
Lemma machineSetReg_relation s t reg value : reg < 32 -> target_state_rel riscvTarget t s ->
 target_state_rel riscvTarget (set_regs (fun n => if decide (n = reg) then value else regs t n) t)
  (machineSetReg s reg value).
Proof.
 intros Hr [Hok [Hpc [Hmem [Hregs Hfp]]]].
 apply conj; [exact Hok|]. apply conj; [exact Hpc|]. apply conj; [exact Hmem|].
 apply conj; [|intros i Hi; change (i < 0) in Hi; lia].
 intros n Hn; pose proof (Hregs n Hn) as He; destruct Hn as [Hnl Hna]; change (n < 32) in Hnl.
 change ((if bool_decide (riscv_state_procID s = riscv_state_procID s) &&
 bool_decide ((n2w n : word 5) = n2w reg) then value else riscv_state_c_gpr s (riscv_state_procID s) (n2w n)) =
 (if decide (n = reg) then value else regs t n)).
 rewrite (proj2 (bool_decide_spec _) eq_refl); cbn [andb].
 destruct (decide (n = reg)) as [->|Hne].
 - rewrite (proj2 (bool_decide_spec _) eq_refl); reflexivity.
 - assert (Hword : (n2w n : word 5) <> n2w reg).
   { intro E; apply (f_equal (@w2n 5)) in E; rewrite !w2n_n2w in E.
     change (n mod 32 = reg mod 32) in E; rewrite !N.mod_small in E by lia; contradiction. }
   rewrite (machine_bool_false _ Hword); exact He.
Qed.

Lemma writeBytearray_asm address bytes memory :
 writeBytearray address bytes memory = asm_write_bytearray address bytes memory.
Proof.
 revert address; induction bytes as [|head rest IH]; intro address; [reflexivity|].
 apply functional_extensionality; intro a; cbn [writeBytearray asm_write_bytearray]; unfold UPDATE.
 destruct (decide (a = address)) as [->|Hne].
 - rewrite (proj2 (bool_decide_spec _) eq_refl); destruct (decide (address = address)); congruence.
 - rewrite (machine_bool_false _ Hne); destruct (decide (address = a)); [congruence|].
   rewrite IH; reflexivity.
Qed.
Theorem writeBytearray_congr (address : word 64) bytes left right (domain : word 64 -> Prop) :
 (forall a, domain a -> left a = right a) ->
 forall a, domain a -> asm_write_bytearray address bytes left a = asm_write_bytearray address bytes right a.
Proof. intros H a Ha; apply mem_eq_imp_asm_write_bytearray_eq; apply H; exact Ha. Qed.

Lemma machine_relation_link s t : target_state_rel riscvTarget t s ->
 riscv_state_c_gpr s (riscv_state_procID s) (n2w 1) = regs t 1.
Proof. intros [_ [_ [_ [Hr _]]]]; apply Hr; vm_compute; split; [reflexivity|discriminate]. Qed.
Lemma machine_relation_ptr2 s t : target_state_rel riscvTarget t s ->
 riscv_state_c_gpr s (riscv_state_procID s) (n2w 12) = regs t 12.
Proof. intros [_ [_ [_ [Hr _]]]]; apply Hr; vm_compute; split; [reflexivity|discriminate]. Qed.

Theorem challengeMachineConfig_cacheOk pc program shared names first extra :
 ccache_interfer_ok pc (challengeMachineConfig pc program shared names first extra).
Proof.
 intros ms t k a b [Hrel Halign].
 pose proof (machine_relation_link ms _ Hrel) as Hlink.
 destruct Hrel as [Hok [Hpc [Hmem [Hregs Hfp]]]].
 change (aligned 2 (regs t 1) = true) in Halign.
 apply conj.
 - change (riscvOk (machineSetPc ms (riscv_state_c_gpr ms (riscv_state_procID ms) (n2w 1))) = true).
   apply machineSetPc_ok; [exact Hok|rewrite Hlink; exact Halign].
 - apply conj.
   + change (riscv_state_c_PC (machineSetPc ms (riscv_state_c_gpr ms (riscv_state_procID ms) (n2w 1)))
      (riscv_state_procID (machineSetPc ms (riscv_state_c_gpr ms (riscv_state_procID ms) (n2w 1)))) = regs t 1).
     rewrite machineSetPc_pc; exact Hlink.
   + apply conj; [exact Hmem|].
     intros r [_ [Hr Ha]]; apply Hregs; split; assumption.
Qed.

Lemma machineExtReturn_contract s t bytes : target_state_rel riscvTarget t s ->
 aligned 2 (regs t 1) = true ->
 riscvOk (machineExtReturn s bytes) = true /\
 get_pc riscvTarget (machineExtReturn s bytes) = regs t 1 /\
 (forall a, pred_set.IN a (mem_domain t) ->
 get_byte riscvTarget (machineExtReturn s bytes) a = asm_write_bytearray (regs t 12) bytes (mem t) a) /\
 (forall r, r < reg_count (config riscvTarget) /\ ~ MEM r (avoid_regs (config riscvTarget)) ->
 get_reg riscvTarget (machineExtReturn s bytes) r = regs t r).
Proof.
 intros Hrel Halign; pose proof (machine_relation_link s t Hrel) as Hlink.
 pose proof (machine_relation_ptr2 s t Hrel) as Hptr.
 destruct Hrel as [Hok [Hpc [Hmem [Hregs Hfp]]]].
 apply conj.
 - unfold machineExtReturn; apply machineSetPc_ok.
   + rewrite machineMemory_ok; exact Hok.
   + rewrite Hlink; exact Halign.
 - apply conj.
   + change (riscv_state_c_PC (machineExtReturn s bytes) (riscv_state_procID (machineExtReturn s bytes)) = regs t 1).
     unfold machineExtReturn; rewrite machineSetPc_pc; exact Hlink.
   + apply conj; [|exact Hregs].
     intros a Ha; change (writeBytearray (riscv_state_c_gpr s (riscv_state_procID s) (n2w 12)) bytes (riscv_state_MEM8 s) a = asm_write_bytearray (regs t 12) bytes (mem t) a).
     rewrite writeBytearray_asm,Hptr; apply mem_eq_imp_asm_write_bytearray_eq; apply Hmem; exact Ha.
Qed.

Lemma machineMmioInfo_noExternalLookup pc first extra index : index < first ->
 ALOOKUP (machineMmioInfo pc first extra) index = None.
Proof.
 intro Hi; apply ALOOKUP_None_iff; intro Hin.
 apply in_map_iff in Hin as [[key value] [He Hin]]; cbn in He; subst key.
 unfold machineMmioInfo in Hin; apply in_combine_l in Hin.
 apply in_map_iff in Hin as [j [He Hj]]; lia.
Qed.
Lemma mmioRecordValid_witness pc first extra index : mmioRecordValid pc first extra index = true ->
 exists info, ALOOKUP (machineMmioInfo pc first extra) index = Some info /\
 fst (snd (snd info)) < 32 /\ aligned 2 (snd (snd (snd info))) = true.
Proof.
 unfold mmioRecordValid; destruct (ALOOKUP (machineMmioInfo pc first extra) index) as [info|] eqn:E;
 [|discriminate]. intro H; apply andb_true_iff in H as [Hr Ha]; apply N.ltb_lt in Hr; eauto.
Qed.

Theorem challengeMachineConfig_ffiOk pc program shared names first extra :
 mmio_pcs_min_index names = Some first ->
 (forall index, index < first -> ALOOKUP (machineMmioInfo pc first extra) index = None) ->
 (forall index, first <= index -> index < LENGTH names -> exists info,
 ALOOKUP (machineMmioInfo pc first extra) index = Some info /\
 fst (snd (snd info)) < 32 /\ aligned 2 (snd (snd (snd info))) = true) ->
 ffi_interfer_ok pc (challengeMachineConfig pc program shared names first extra).
Proof.
 intros Hfirst Hext Hmmio ms k index newBytes t bytes bytes2 i [Hindex [Hi Hdomain]].
 change (mmio_pcs_min_index names = Some i) in Hi; rewrite Hfirst in Hi; injection Hi as <-.
 change (index < LENGTH names) in Hindex; split.
 - intros Hbefore [_ [_ [_ [Hrel Halign]]]].
   change (aligned 2 (regs t 1) = true) in Halign.
   pose proof (machineExtReturn_contract ms _ newBytes Hrel Halign) as Hreturn.
   change (let ms' := machineFfiInterference names (machineMmioInfo pc first extra) k (index,(newBytes,ms)) in
    riscvOk ms' /\ get_pc riscvTarget ms' = regs t 1 /\
    (forall ad, pred_set.IN ad (mem_domain t) -> get_byte riscvTarget ms' ad =
      asm_write_bytearray (regs t 12) newBytes (mem t) ad) /\
    (forall r, MEM r [24;25;26] /\ r < reg_count (config riscvTarget) /\
      ~ MEM r (avoid_regs (config riscvTarget)) -> get_reg riscvTarget ms' r = regs t r)).
   unfold machineFfiInterference; cbn; rewrite Hext by exact Hbefore.
   destruct Hreturn as [Hok [Hpc [Hmem Hregs]]].
   apply conj; [exact Hok|]. apply conj; [exact Hpc|]. apply conj; [exact Hmem|].
   intros r [_ Hr]; exact (Hregs r Hr).
 - intros [Hafter Hrel]; destruct (Hmmio index Hafter Hindex) as [info [Hlookup [Hreg Halign]]].
   exists info; apply conj; [exact Hlookup|]. split.
   + intros Hname returned; change (EL index names = SharedMem MappedRead) in Hname.
     change (target_state_rel riscvTarget
      (set_regs (fun n => if decide (n = fst (snd (snd info))) then word_of_bytes false (n2w 0) returned else regs t n)
       (set_pc (snd (snd (snd info))) t))
      (machineFfiInterference names (machineMmioInfo pc first extra) k (index,(returned,ms)))).
     unfold machineFfiInterference; cbn; rewrite Hlookup; unfold machineMmioReturn; rewrite Hname.
     rewrite (proj2 (bool_decide_spec _) eq_refl).
     pose proof (machineSetReg_relation ms _ _ (word_of_bytes false (n2w 0) returned) Hreg Hrel) as Hr.
     pose proof (machineSetPc_relation _ _ _ Halign Hr) as Hp; exact Hp.
   + intro Hname; change (EL index names = SharedMem MappedWrite) in Hname.
     change (target_state_rel riscvTarget (set_pc (snd (snd (snd info))) t)
      (machineFfiInterference names (machineMmioInfo pc first extra) k (index,(newBytes,ms)))).
     unfold machineFfiInterference; cbn; rewrite Hlookup; unfold machineMmioReturn; rewrite Hname.
     change (bool_decide (SharedMem MappedWrite = SharedMem MappedRead)) with false; cbn.
     pose proof (machineSetPc_relation ms _ _ Halign Hrel) as Hp; exact Hp.
Qed.
Theorem challengeMachineConfig_ffiOk_checked pc program shared names first extra :
 mmio_pcs_min_index names = Some first ->
 (forall index, index < LENGTH names -> first <= index -> mmioRecordValid pc first extra index = true) ->
 ffi_interfer_ok pc (challengeMachineConfig pc program shared names first extra).
Proof.
 intros Hfirst Hcheck; apply challengeMachineConfig_ffiOk; [exact Hfirst|apply machineMmioInfo_noExternalLookup|].
 intros index Hlo Hhi; apply mmioRecordValid_witness; apply Hcheck; assumption.
Qed.

(** The executable name boundary determines the unique upstream MMIO boundary. *)
Theorem ffiNameBoundary_min_index names first : ffiNameBoundaryValid names first ->
 mmio_pcs_min_index names = Some first.
Proof.
 intros [Hsize Hnames].
 set (P := fun x => x <= LENGTH names /\
  (forall j, j < x -> exists name, EL j names = ExtCall name) /\
  (forall j, x <= j /\ j < LENGTH names -> exists op, EL j names = SharedMem op)).
 assert (Hfirst : P first).
 { split; [exact Hsize|]; split.
   - intros j Hj; pose proof (Hnames j ltac:(lia)) as Hname.
     destruct (EL j names) as [name|op] eqn:E; [exists name; reflexivity|lia].
   - intros j [Hlo Hhi]; pose proof (Hnames j Hhi) as Hname.
     destruct (EL j names) as [name|op] eqn:E; [lia|exists op; reflexivity]. }
 assert (Hunique : forall x, P x -> x = first).
 { intros x [Hx [Hext Hshared]]; destruct (N.lt_trichotomy x first) as [Hlt|[Heq|Hgt]]; [|exact Heq|].
   - destruct (Hshared x (conj (N.le_refl x) (N.lt_le_trans x first (LENGTH names) Hlt Hsize))) as [op E].
     pose proof (Hnames x ltac:(lia)) as Hname; rewrite E in Hname; lia.
   - destruct (Hext first Hgt) as [name E].
     pose proof (Hnames first ltac:(lia)) as Hname; rewrite E in Hname; lia. }
 unfold mmio_pcs_min_index; change (some P = Some first); unfold some.
 destruct (classical_dec (exists x, P x)) as [Hex|Hnone].
 - f_equal; apply Hunique; apply select_spec; exact Hex.
 - exfalso; apply Hnone; exists first; exact Hfirst.
Qed.
Theorem baseline_mmio_min_index : mmio_pcs_min_index baselineNames = Some baselineFirst.
Proof. apply ffiNameBoundary_min_index; exact baseline_name_boundary. Qed.
Theorem baseline_machine_ffiOk :
 ffi_interfer_ok (n2w nativePc) (machineConfig baselineSubmission).
Proof.
 rewrite baselineSubmission_machine_config; apply challengeMachineConfig_ffiOk_checked.
 - exact baseline_mmio_min_index.
 - exact baseline_mmio_valid.
Qed.
Theorem baseline_machine_cacheOk :
 ccache_interfer_ok (n2w nativePc) (machineConfig baselineSubmission).
Proof. rewrite baselineSubmission_machine_config; apply challengeMachineConfig_cacheOk. Qed.
