(** Actual original bootstrap tail, executed over arbitrary incoming memory.
    Domain/alignment obligations are separated from the unconditional writes. *)
From Galette Require Import Base.
From Stdlib Require Import List NArith Lia.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.n_bit Require Import words alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.relation Require Import relation.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import inst.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From InitE.Guest Require Import Bookkeeping.
From InitE.InitE Require Import Parameters BaselineArtifactLayout SubmissionModel.
From InitE.Baseline Require Import BootstrapProgram BootstrapMemory BootstrapSteps BootstrapPrefix BootstrapCopy BootstrapMemoryControl BootstrapCodeFacts.
Open Scope N_scope.
Definition tailCode : list (asm.asm 64) := MAP snd (DROP 8 bootstrapBlocks).

Definition tailInstructions : list (asm.asm 64) := Eval vm_compute in tailCode.
Theorem tail_code_list : tailCode = tailInstructions.
Proof. vm_compute; reflexivity. Qed.

(** A pure eight-byte memory update. The auxiliary state's domain affects only
    failure, never its memory; [tail_put_memory] proves that independence. *)
Definition tailPut (p value : word 64) (memory : word 64 -> word 8) : word 64 -> word 8 :=
 mem (write_mem_word p 8 value
  (mk_asm_state (fun _ => n2w 0) (fun _ => n2w 0) memory
   (fun _ => True) (n2w 0) 1 2 false false)).
Lemma tail_put_memory p value (s : asm_state 64) : be s = false ->
 mem (write_mem_word p 8 value s) = tailPut p value (mem s).
Proof.
 intro Hb; apply functional_extensionality; intro x.
 destruct (classic (exists j, j < 8 /\ x = (p+n2w j)%w)) as [[j [Hj ->]]|Hout].
 - unfold tailPut.
   replace (p+n2w j)%w with (offs (be s) p j) at 1 by (unfold offs; rewrite Hb; reflexivity).
   rewrite write_mem_word_mem_in by (try exact Hj; vm_compute; discriminate).
   change ((w2w (value >>> (8*j))%w : word 8) = mem (write_mem_word p 8 value
    (mk_asm_state (fun _ => n2w 0) (fun _ => n2w 0) (mem s)
     (fun _ => True) (n2w 0) 1 2 false false)) (offs false p j)).
   rewrite write_mem_word_mem_in by (try exact Hj; vm_compute; discriminate); reflexivity.
 - unfold tailPut; rewrite !write_mem_word_mem_out; try reflexivity.
   + intros j Hj; change (x <> (p+n2w j)%w); intro E; apply Hout; exists j; auto.
   + intros j Hj; unfold offs; rewrite Hb; intro E; apply Hout; exists j; auto.
Qed.
Lemma tail_put_in p value memory j : j < 8 ->
 tailPut p value memory (p+n2w j)%w = (w2w (value >>> (8*j))%w : word 8).
Proof.
 intro Hj; unfold tailPut; change (p+n2w j)%w with (offs false p j).
 apply write_mem_word_mem_in; [vm_compute; discriminate|exact Hj].
Qed.
Lemma tail_put_out p value memory x :
 (forall j, j < 8 -> x <> (p+n2w j)%w) -> tailPut p value memory x = memory x.
Proof.
 intro H; unfold tailPut; apply write_mem_word_mem_out; exact H.
Qed.
Lemma tail_store_memory (s : asm_state 64) r base offset : be s = false ->
 mem (mem_store 8 r (Addr base offset) s) =
 tailPut (regs s base+offset)%w (regs s r) (mem s).
Proof.
 intro Hb; unfold mem_store,addr,read_reg; rewrite Hb,assert_memory; apply tail_put_memory; exact Hb.
Qed.
Lemma tail_after_be (s : asm_state 64) i : be (after s i) = be s.
Proof. exact ((proj1) (asm_consts i _ s)). Qed.
Lemma tail_after_lr (s : asm_state 64) i : lr (after s i) = lr s.
Proof. exact ((fun H => proj1 (proj2 H)) (asm_consts i _ s)). Qed.
Lemma tail_after_align (s : asm_state 64) i : align (after s i) = align s.
Proof. exact ((fun H => proj1 (proj2 (proj2 H))) (asm_consts i _ s)). Qed.
Lemma tail_after_mem_domain (s : asm_state 64) i : mem_domain (after s i) = mem_domain s.
Proof. exact ((fun H => proj2 (proj2 (proj2 H))) (asm_consts i _ s)). Qed.
Lemma tail_loc_pc (s : asm_state 64) r (value : word 64) :
 pc (after s (Loc r value)) = (pc s+n2w (LENGTH (riscv_target.riscv_enc (Loc r value))))%w.
Proof. reflexivity. Qed.
Lemma tail_loc_regs (s : asm_state 64) r (value : word 64) :
 regs (after s (Loc r value)) = UPDATE r (pc s+value)%w (regs s).
Proof. reflexivity. Qed.
Lemma tail_loc_mem (s : asm_state 64) r (value : word 64) :
 mem (after s (Loc r value)) = mem s.
Proof. reflexivity. Qed.
Lemma tail_loc_fp_regs (s : asm_state 64) r (value : word 64) :
 fp_regs (after s (Loc r value)) = fp_regs s.
Proof. reflexivity. Qed.
Lemma tail_loc_failed (s : asm_state 64) r (value : word 64) :
 failed (after s (Loc r value)) = failed s.
Proof. reflexivity. Qed.
Lemma tail_const_pc (s : asm_state 64) r (value : word 64) :
 pc (after s (Inst (Const r value))) = (pc s+n2w (LENGTH (riscv_target.riscv_enc (Inst (Const r value)))))%w.
Proof. reflexivity. Qed.
Lemma tail_const_regs (s : asm_state 64) r (value : word 64) :
 regs (after s (Inst (Const r value))) = UPDATE r value (regs s).
Proof. reflexivity. Qed.
Lemma tail_const_mem (s : asm_state 64) r (value : word 64) :
 mem (after s (Inst (Const r value))) = mem s.
Proof. reflexivity. Qed.
Lemma tail_const_fp_regs (s : asm_state 64) r (value : word 64) :
 fp_regs (after s (Inst (Const r value))) = fp_regs s.
Proof. reflexivity. Qed.
Lemma tail_const_failed (s : asm_state 64) r (value : word 64) :
 failed (after s (Inst (Const r value))) = failed s.
Proof. reflexivity. Qed.
Lemma tail_shift_pc (s : asm_state 64) r (value : word 64) :
 pc (after s (Inst (Arith (Shift Lsl r r (Imm value))))) = (pc s+n2w (LENGTH (riscv_target.riscv_enc (Inst (Arith (Shift Lsl r r (Imm value)))))))%w.
Proof. reflexivity. Qed.
Lemma tail_shift_regs (s : asm_state 64) r (value : word 64) :
 regs (after s (Inst (Arith (Shift Lsl r r (Imm value))))) = UPDATE r (word_lsl (regs s r) (w2n value)) (regs s).
Proof. reflexivity. Qed.
Lemma tail_shift_mem (s : asm_state 64) r (value : word 64) :
 mem (after s (Inst (Arith (Shift Lsl r r (Imm value))))) = mem s.
Proof. reflexivity. Qed.
Lemma tail_shift_fp_regs (s : asm_state 64) r (value : word 64) :
 fp_regs (after s (Inst (Arith (Shift Lsl r r (Imm value))))) = fp_regs s.
Proof. reflexivity. Qed.
Lemma tail_shift_failed (s : asm_state 64) r (value : word 64) :
 failed (after s (Inst (Arith (Shift Lsl r r (Imm value))))) = failed s.
Proof. reflexivity. Qed.
Lemma tail_jump_pc (s : asm_state 64) (value : word 64) :
 pc (after s (Jump value)) = (pc s+value)%w.
Proof. reflexivity. Qed.
Lemma tail_jump_regs (s : asm_state 64) (value : word 64) :
 regs (after s (Jump value)) = regs s.
Proof. reflexivity. Qed.
Lemma tail_jump_mem (s : asm_state 64) (value : word 64) :
 mem (after s (Jump value)) = mem s.
Proof. reflexivity. Qed.
Lemma tail_jump_fp_regs (s : asm_state 64) (value : word 64) :
 fp_regs (after s (Jump value)) = fp_regs s.
Proof. reflexivity. Qed.
Lemma tail_jump_failed (s : asm_state 64) (value : word 64) :
 failed (after s (Jump value)) = failed s.
Proof. reflexivity. Qed.
Lemma tail_store_pc (s : asm_state 64) r (address : asm.addr 64) :
 pc (after s (Inst (Mem Store r address))) = (pc s+n2w (LENGTH (riscv_target.riscv_enc (Inst (Mem Store r address)))))%w.
Proof. reflexivity. Qed.
Lemma tail_asm_store_regs {width} r (address : asm.addr width) next (s : asm_state width) :
 regs (asmSem.asm (Inst (Mem Store r address)) next s) = regs s.
Proof. change (regs (mem_store (dimindex width / 8) r address s) = regs s). unfold mem_store; cbv zeta; rewrite asm_assert_registers; apply write_mem_word_regs. Qed.
Lemma tail_asm_store_fp_regs {width} r (address : asm.addr width) next (s : asm_state width) :
 fp_regs (asmSem.asm (Inst (Mem Store r address)) next s) = fp_regs s.
Proof. change (fp_regs (mem_store (dimindex width / 8) r address s) = fp_regs s). unfold mem_store; cbv zeta; unfold assert,set_failed; cbn [fp_regs]; apply write_mem_word_regs. Qed.
Lemma tail_store_regs (s : asm_state 64) r (address : asm.addr 64) :
 regs (after s (Inst (Mem Store r address))) = regs s.
Proof. unfold after; apply tail_asm_store_regs. Qed.
Lemma tail_store_fp_regs (s : asm_state 64) r (address : asm.addr 64) :
 fp_regs (after s (Inst (Mem Store r address))) = fp_regs s.
Proof. unfold after; apply tail_asm_store_fp_regs. Qed.
Lemma tail_asm_store_memory {width} r (address : asm.addr width) next (s : asm_state width) :
 mem (asmSem.asm (Inst (Mem Store r address)) next s) =
 mem (mem_store (dimindex width / 8) r address s).
Proof. reflexivity. Qed.
Lemma tail_after_store_memory (s : asm_state 64) r base offset : be s = false ->
 mem (after s (Inst (Mem Store r (Addr base offset)))) =
 tailPut (regs s base+offset)%w (regs s r) (mem s).
Proof. unfold after; rewrite tail_asm_store_memory; apply tail_store_memory. Qed.

Local Opaque tailPut after.

Definition tailMemory (memory : word 64 -> word 8) : word 64 -> word 8 :=
 tailPut (n2w (sourceBase+32)) (n2w codeBufferLimit)
 (tailPut (n2w (sourceBase+24)) (n2w codeBufferEnd)
 (tailPut (n2w (sourceBase+16)) (n2w initDataEnd)
 (tailPut (n2w (sourceBase+8)) (n2w initDataEnd)
 (tailPut (n2w sourceBase) (n2w (initDataRam+24))
 (tailPut (n2w (initDataRam+16)) (n2w ramEnd)
 (tailPut (n2w (initDataRam+8)) (n2w stackStart)
 (tailPut (n2w initDataRam) (n2w sourceBase) memory))))))).
Definition tailRegisters (rs : N -> word 64) : N -> word 64 :=
 fun r => if r =? 5 then n2w sourceBase
 else if r =? 6 then n2w codeBufferLimit
 else if r =? 10 then n2w nativePc
 else if r =? 11 then n2w sourceBase
 else if r =? 12 then n2w stackStart
 else if r =? 13 then n2w ramEnd else rs r.

Ltac tail_expand := rewrite tail_code_list; cbn [tailInstructions runCode bootLoc bootConst bootShift bootStore].
Ltac tail_controls := repeat first [rewrite tail_after_be | rewrite tail_after_lr |
 rewrite tail_after_align | rewrite tail_after_mem_domain].
Ltac tail_pc_regs := repeat first [rewrite updateN_eqb; repeat match goal with H : (?x =? ?y) = _ |- _ => progress rewrite H end; cbn [N.eqb Pos.eqb] | rewrite tail_loc_pc | rewrite tail_const_pc |
 rewrite tail_shift_pc | rewrite tail_store_pc | rewrite tail_jump_pc |
 rewrite tail_loc_regs | rewrite tail_const_regs | rewrite tail_shift_regs |
 rewrite tail_store_regs | rewrite tail_jump_regs].

Theorem tail_control (s : asm_state 64) : pc s = n2w 0x8000002c ->
 pc (runCode tailCode s) = n2w nativePc /\
 regs (runCode tailCode s) = tailRegisters (regs s) /\
 fp_regs (runCode tailCode s) = fp_regs s /\
 mem_domain (runCode tailCode s) = mem_domain s /\
 lr (runCode tailCode s) = lr s /\
 align (runCode tailCode s) = align s /\
 be (runCode tailCode s) = be s.
Proof.
 intro Hpc; repeat apply conj; tail_expand.
 - tail_pc_regs; try rewrite Hpc; vm_compute; reflexivity.
 - apply functional_extensionality; intro r; unfold tailRegisters.
   destruct (r =? 5) eqn:E5.
   + apply N.eqb_eq in E5; subst r; tail_pc_regs; try rewrite Hpc; vm_compute; reflexivity.
   + destruct (r =? 6) eqn:E6.
     * apply N.eqb_eq in E6; subst r; tail_pc_regs; try rewrite Hpc; vm_compute; reflexivity.
     * destruct (r =? 10) eqn:E10.
       -- apply N.eqb_eq in E10; subst r; tail_pc_regs; try rewrite Hpc; vm_compute; reflexivity.
       -- destruct (r =? 11) eqn:E11.
          ++ apply N.eqb_eq in E11; subst r; tail_pc_regs; try rewrite Hpc; vm_compute; reflexivity.
          ++ destruct (r =? 12) eqn:E12.
             ** apply N.eqb_eq in E12; subst r; tail_pc_regs; try rewrite Hpc; vm_compute; reflexivity.
             ** destruct (r =? 13) eqn:E13.
                --- apply N.eqb_eq in E13; subst r; tail_pc_regs; try rewrite Hpc; vm_compute; reflexivity.
                --- tail_pc_regs; reflexivity.
 - repeat first [rewrite tail_loc_fp_regs | rewrite tail_const_fp_regs |
    rewrite tail_shift_fp_regs | rewrite tail_store_fp_regs | rewrite tail_jump_fp_regs]; reflexivity.
 - tail_controls; reflexivity.
 - tail_controls; reflexivity.
 - tail_controls; reflexivity.
 - tail_controls; reflexivity.
Qed.

Definition tailOffset0 : word 64 := Eval vm_compute in (n2w 0 : word 64).
Definition tailOffset8 : word 64 := Eval vm_compute in (n2w 8 : word 64).
Definition tailOffset16 : word 64 := Eval vm_compute in (n2w 16 : word 64).
Definition tailOffset24 : word 64 := Eval vm_compute in (n2w 24 : word 64).
Definition tailOffset32 : word 64 := Eval vm_compute in (n2w 32 : word 64).
(** The eight actual store operands, proved before rewriting memory so that
    register updates are never duplicated across nested memory functions. *)
Ltac tail_prefix_expand n := rewrite tail_code_list; rewrite TAKE_firstn;
 let count := eval vm_compute in (N.to_nat n) in change (N.to_nat n) with count;
 cbn [tailInstructions firstn runCode bootLoc bootConst bootShift bootStore].
Ltac tail_prefix_in n H := rewrite tail_code_list,TAKE_firstn in H;
 let count := eval vm_compute in (N.to_nat n) in change (N.to_nat n) with count in H;
 cbn [tailInstructions firstn runCode bootLoc bootConst bootShift bootStore] in H.
Lemma tail_site_3 (s : asm_state 64) : pc s = n2w 0x8000002c ->
 (regs (runCode (TAKE 3 tailCode) s) 5+tailOffset0)%w = n2w (initDataRam) /\
 regs (runCode (TAKE 3 tailCode) s) 6 = n2w (sourceBase).
Proof.
 intro Hpc; apply conj; tail_prefix_expand 3; tail_pc_regs; try rewrite Hpc; vm_compute; reflexivity.
Qed.
Lemma tail_site_7 (s : asm_state 64) : pc s = n2w 0x8000002c ->
 (regs (runCode (TAKE 7 tailCode) s) 5+tailOffset0)%w = n2w (initDataRam+8) /\
 regs (runCode (TAKE 7 tailCode) s) 6 = n2w (stackStart).
Proof.
 intro Hpc; apply conj; tail_prefix_expand 7; tail_pc_regs; try rewrite Hpc; vm_compute; reflexivity.
Qed.
Lemma tail_site_11 (s : asm_state 64) : pc s = n2w 0x8000002c ->
 (regs (runCode (TAKE 11 tailCode) s) 5+tailOffset0)%w = n2w (initDataRam+16) /\
 regs (runCode (TAKE 11 tailCode) s) 6 = n2w (ramEnd).
Proof.
 intro Hpc; apply conj; tail_prefix_expand 11; tail_pc_regs; try rewrite Hpc; vm_compute; reflexivity.
Qed.
Lemma tail_site_15 (s : asm_state 64) : pc s = n2w 0x8000002c ->
 (regs (runCode (TAKE 15 tailCode) s) 5+tailOffset0)%w = n2w (sourceBase) /\
 regs (runCode (TAKE 15 tailCode) s) 6 = n2w (initDataRam+24).
Proof.
 intro Hpc; apply conj; tail_prefix_expand 15; tail_pc_regs; try rewrite Hpc; vm_compute; reflexivity.
Qed.
Lemma tail_site_17 (s : asm_state 64) : pc s = n2w 0x8000002c ->
 (regs (runCode (TAKE 17 tailCode) s) 5+tailOffset8)%w = n2w (sourceBase+8) /\
 regs (runCode (TAKE 17 tailCode) s) 6 = n2w (initDataEnd).
Proof.
 intro Hpc; apply conj; tail_prefix_expand 17; tail_pc_regs; try rewrite Hpc; vm_compute; reflexivity.
Qed.
Lemma tail_site_19 (s : asm_state 64) : pc s = n2w 0x8000002c ->
 (regs (runCode (TAKE 19 tailCode) s) 5+tailOffset16)%w = n2w (sourceBase+16) /\
 regs (runCode (TAKE 19 tailCode) s) 6 = n2w (initDataEnd).
Proof.
 intro Hpc; apply conj; tail_prefix_expand 19; tail_pc_regs; try rewrite Hpc; vm_compute; reflexivity.
Qed.
Lemma tail_site_21 (s : asm_state 64) : pc s = n2w 0x8000002c ->
 (regs (runCode (TAKE 21 tailCode) s) 5+tailOffset24)%w = n2w (sourceBase+24) /\
 regs (runCode (TAKE 21 tailCode) s) 6 = n2w (codeBufferEnd).
Proof.
 intro Hpc; apply conj; tail_prefix_expand 21; tail_pc_regs; try rewrite Hpc; vm_compute; reflexivity.
Qed.
Lemma tail_site_23 (s : asm_state 64) : pc s = n2w 0x8000002c ->
 (regs (runCode (TAKE 23 tailCode) s) 5+tailOffset32)%w = n2w (sourceBase+32) /\
 regs (runCode (TAKE 23 tailCode) s) 6 = n2w (codeBufferLimit).
Proof.
 intro Hpc; apply conj; tail_prefix_expand 23; tail_pc_regs; try rewrite Hpc; vm_compute; reflexivity.
Qed.
Theorem tail_memory (s : asm_state 64) : pc s = n2w 0x8000002c -> be s = false ->
 mem (runCode tailCode s) = tailMemory (mem s).
Proof.
 intros Hpc Hb.
 pose proof (tail_site_3 s Hpc) as [Ha3 Hv3].
 tail_prefix_in 3 Ha3; tail_prefix_in 3 Hv3. unfold tailOffset0 in Ha3.
 pose proof (tail_site_7 s Hpc) as [Ha7 Hv7].
 tail_prefix_in 7 Ha7; tail_prefix_in 7 Hv7. unfold tailOffset0 in Ha7.
 pose proof (tail_site_11 s Hpc) as [Ha11 Hv11].
 tail_prefix_in 11 Ha11; tail_prefix_in 11 Hv11. unfold tailOffset0 in Ha11.
 pose proof (tail_site_15 s Hpc) as [Ha15 Hv15].
 tail_prefix_in 15 Ha15; tail_prefix_in 15 Hv15. unfold tailOffset0 in Ha15.
 pose proof (tail_site_17 s Hpc) as [Ha17 Hv17].
 tail_prefix_in 17 Ha17; tail_prefix_in 17 Hv17. unfold tailOffset8 in Ha17.
 pose proof (tail_site_19 s Hpc) as [Ha19 Hv19].
 tail_prefix_in 19 Ha19; tail_prefix_in 19 Hv19. unfold tailOffset16 in Ha19.
 pose proof (tail_site_21 s Hpc) as [Ha21 Hv21].
 tail_prefix_in 21 Ha21; tail_prefix_in 21 Hv21. unfold tailOffset24 in Ha21.
 pose proof (tail_site_23 s Hpc) as [Ha23 Hv23].
 tail_prefix_in 23 Ha23; tail_prefix_in 23 Hv23. unfold tailOffset32 in Ha23.
 tail_expand.
 repeat first [rewrite tail_loc_mem | rewrite tail_const_mem | rewrite tail_shift_mem |
  rewrite tail_jump_mem | rewrite tail_after_store_memory by (tail_controls; exact Hb)].
 rewrite Ha3,Hv3,Ha7,Hv7,Ha11,Hv11,Ha15,Hv15,Ha17,Hv17,Ha19,Hv19,Ha21,Hv21,Ha23,Hv23.
 unfold tailMemory; reflexivity.
Qed.

Definition tailHeaders : list (N * word 64) :=
 [(initDataRam,n2w sourceBase);(initDataRam+8,n2w stackStart);(initDataRam+16,n2w ramEnd);
  (sourceBase,n2w (initDataRam+24));(sourceBase+8,n2w initDataEnd);
  (sourceBase+16,n2w initDataEnd);(sourceBase+24,n2w codeBufferEnd);(sourceBase+32,n2w codeBufferLimit)].

Lemma tail_word_apart a b j k : a+8 <= b \/ b+8 <= a ->
 a+8 < 2^64 -> b+8 < 2^64 -> j < 8 -> k < 8 ->
 (n2w a+n2w j : word 64)%w <> (n2w b+n2w k)%w.
Proof.
 intros Hapart Ha Hb Hj Hk E; apply (f_equal w2n) in E.
 rewrite !word_add_n2w,!w2n_n2w in E.
 change (dimword 64) with (2^64) in E.
 rewrite !N.mod_small in E by lia; lia.
Qed.
Ltac tail_address_numbers := cbv [initDataRam sourceBase stackStart ramEnd ramStart ramSize
 initDataEnd bitmapWordCount codeBufferEnd nativePc nativeByteCount codeBufferLimit].
Theorem tail_memory_headers memory address value : In (address,value) tailHeaders ->
 forall j, j < 8 -> tailMemory memory (n2w address+n2w j)%w =
 (w2w (value >>> (8*j))%w : word 8).
Proof.
 unfold tailHeaders; intros Hin j Hj.
 repeat destruct Hin as [Hin|Hin]; try contradiction; inversion Hin; subst; clear Hin;
 unfold tailMemory.
 - rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   apply tail_put_in; exact Hj.
 - rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   apply tail_put_in; exact Hj.
 - rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   apply tail_put_in; exact Hj.
 - rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   apply tail_put_in; exact Hj.
 - rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   apply tail_put_in; exact Hj.
 - rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   apply tail_put_in; exact Hj.
 - rewrite tail_put_out.
   2:{ intros k Hk; apply tail_word_apart; try assumption; tail_address_numbers; lia. }
   apply tail_put_in; exact Hj.
 -
   apply tail_put_in; exact Hj.
Qed.

Definition tailAddresses : list N := MAP fst tailHeaders.
Definition tailWritten (x : word 64) : Prop :=
 exists address, In address tailAddresses /\ exists j, j < 8 /\ x = (n2w address+n2w j)%w.
Theorem tailMemory_frame memory x : ~ tailWritten x -> tailMemory memory x = memory x.
Proof.
 intro Hout; unfold tailMemory; rewrite !tail_put_out; try reflexivity.
 all: intros j Hj E; apply Hout; unfold tailWritten;
  match type of E with ?point = (n2w ?address+n2w ?offset)%w => exists address end;
  split; [unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto|exists j; auto].
Qed.
Theorem tail_memory_frame (s : asm_state 64) x :
 pc s = n2w 0x8000002c -> be s = false -> ~ tailWritten x ->
 mem (runCode tailCode s) x = mem s x.
Proof. intros Hp Hb Ho; rewrite tail_memory by assumption; apply tailMemory_frame; exact Ho. Qed.

Lemma tail_ram_domain (a : word 64) :
 (initDataRam <= w2n a /\ w2n a < initDataRam+24) \/
 (sourceBase <= w2n a /\ w2n a < sourceBase+40) -> bootstrapDomain a.
Proof.
 intro H; unfold bootstrapDomain; split.
 - unfold submissionMemoryDomain,submissionSharedDomain; split.
   + right; cbv [initDataRam sourceBase ramStart ramEnd ramSize] in *; lia.
   + cbv [initDataRam sourceBase inputStart inputEnd inputSize outputStart outputEnd outputSize] in *.
     intros [[H1 H2]|[H1 H2]]; lia.
 - intros i Hi E.
   assert (Hin : In i (COUNT_LIST 4)) by (apply bootstrap_count_in; exact Hi).
   assert (Hslot : w2n ((n2w nativePc-n2w (16*(i+1)))%w : word 64) < initDataRam).
   { vm_compute in Hin; repeat destruct Hin as [Hin|Hin]; try contradiction;
     subst i; vm_compute; congruence. }
   rewrite <- E in Hslot; cbv [initDataRam sourceBase] in *; lia.
Qed.
Lemma tail_addresses_domain address j : In address tailAddresses -> j < 8 ->
 bootstrapDomain (n2w address+n2w j)%w.
Proof.
 unfold tailAddresses,tailHeaders; cbn [MAP fst]; intros Hin Hj.
 repeat destruct Hin as [Hin|Hin]; try contradiction; subst address;
 apply tail_ram_domain; rewrite word_add_n2w,w2n_n2w;
 change (dimword 64) with (2^64);
 rewrite N.mod_small by (tail_address_numbers; lia); tail_address_numbers; lia.
Qed.
Lemma tail_addresses_aligned address : In address tailAddresses ->
 aligned 3 (n2w address : word 64) = true.
Proof.
 unfold tailAddresses,tailHeaders; cbn [MAP fst]; intros Hin;
 repeat destruct Hin as [Hin|Hin]; try contradiction; subst address; vm_compute; reflexivity.
Qed.
Lemma tail_store_failed (s : asm_state 64) r base offset : be s = false ->
 (forall j, j < 8 -> mem_domain s ((regs s base+offset)+n2w j)%w) ->
 aligned 3 (regs s base+offset)%w = true ->
 failed (mem_store 8 r (Addr base offset) s) = failed s.
Proof.
 intros Hb Hd Ha; unfold mem_store,addr,read_reg; rewrite Hb.
 change (LOG2 8) with 3; rewrite Ha,assert_failure; cbn [negb orb].
 apply write_mem_word_failed; intros j Hj; unfold offs; rewrite Hb; apply Hd; exact Hj.
Qed.
Lemma tail_asm_store_failed {width} r (address : asm.addr width) next (s : asm_state width) :
 failed (asmSem.asm (Inst (Mem Store r address)) next s) =
 failed (mem_store (dimindex width / 8) r address s).
Proof. reflexivity. Qed.
Local Transparent after.
Lemma tail_after_store_failed (s : asm_state 64) r base offset : be s = false ->
 (forall j, j < 8 -> mem_domain s ((regs s base+offset)+n2w j)%w) ->
 aligned 3 (regs s base+offset)%w = true ->
 failed (after s (Inst (Mem Store r (Addr base offset)))) = failed s.
Proof. unfold after; rewrite tail_asm_store_failed; apply tail_store_failed. Qed.
Local Opaque after.
Lemma tail_fail_site_3 (s : asm_state 64) :
 pc s = n2w 0x8000002c -> be s = false -> mem_domain s = bootstrapDomain ->
 failed (after (runCode (TAKE 3 tailCode) s) (Inst (Mem Store 6 (Addr 5 tailOffset0)))) =
 failed (runCode (TAKE 3 tailCode) s).
Proof.
 intros Hp Hb Hd; pose proof (tail_site_3 s Hp) as [Ha _]; apply tail_after_store_failed.
 - tail_prefix_expand 3; tail_controls; exact Hb.
 - intros j Hj; rewrite Ha; tail_prefix_expand 3; tail_controls; rewrite Hd;
   apply tail_addresses_domain; [unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto|exact Hj].
 - rewrite Ha; apply tail_addresses_aligned; unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto.
Qed.
Lemma tail_fail_site_7 (s : asm_state 64) :
 pc s = n2w 0x8000002c -> be s = false -> mem_domain s = bootstrapDomain ->
 failed (after (runCode (TAKE 7 tailCode) s) (Inst (Mem Store 6 (Addr 5 tailOffset0)))) =
 failed (runCode (TAKE 7 tailCode) s).
Proof.
 intros Hp Hb Hd; pose proof (tail_site_7 s Hp) as [Ha _]; apply tail_after_store_failed.
 - tail_prefix_expand 7; tail_controls; exact Hb.
 - intros j Hj; rewrite Ha; tail_prefix_expand 7; tail_controls; rewrite Hd;
   apply tail_addresses_domain; [unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto|exact Hj].
 - rewrite Ha; apply tail_addresses_aligned; unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto.
Qed.
Lemma tail_fail_site_11 (s : asm_state 64) :
 pc s = n2w 0x8000002c -> be s = false -> mem_domain s = bootstrapDomain ->
 failed (after (runCode (TAKE 11 tailCode) s) (Inst (Mem Store 6 (Addr 5 tailOffset0)))) =
 failed (runCode (TAKE 11 tailCode) s).
Proof.
 intros Hp Hb Hd; pose proof (tail_site_11 s Hp) as [Ha _]; apply tail_after_store_failed.
 - tail_prefix_expand 11; tail_controls; exact Hb.
 - intros j Hj; rewrite Ha; tail_prefix_expand 11; tail_controls; rewrite Hd;
   apply tail_addresses_domain; [unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto|exact Hj].
 - rewrite Ha; apply tail_addresses_aligned; unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto.
Qed.
Lemma tail_fail_site_15 (s : asm_state 64) :
 pc s = n2w 0x8000002c -> be s = false -> mem_domain s = bootstrapDomain ->
 failed (after (runCode (TAKE 15 tailCode) s) (Inst (Mem Store 6 (Addr 5 tailOffset0)))) =
 failed (runCode (TAKE 15 tailCode) s).
Proof.
 intros Hp Hb Hd; pose proof (tail_site_15 s Hp) as [Ha _]; apply tail_after_store_failed.
 - tail_prefix_expand 15; tail_controls; exact Hb.
 - intros j Hj; rewrite Ha; tail_prefix_expand 15; tail_controls; rewrite Hd;
   apply tail_addresses_domain; [unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto|exact Hj].
 - rewrite Ha; apply tail_addresses_aligned; unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto.
Qed.
Lemma tail_fail_site_17 (s : asm_state 64) :
 pc s = n2w 0x8000002c -> be s = false -> mem_domain s = bootstrapDomain ->
 failed (after (runCode (TAKE 17 tailCode) s) (Inst (Mem Store 6 (Addr 5 tailOffset8)))) =
 failed (runCode (TAKE 17 tailCode) s).
Proof.
 intros Hp Hb Hd; pose proof (tail_site_17 s Hp) as [Ha _]; apply tail_after_store_failed.
 - tail_prefix_expand 17; tail_controls; exact Hb.
 - intros j Hj; rewrite Ha; tail_prefix_expand 17; tail_controls; rewrite Hd;
   apply tail_addresses_domain; [unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto|exact Hj].
 - rewrite Ha; apply tail_addresses_aligned; unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto.
Qed.
Lemma tail_fail_site_19 (s : asm_state 64) :
 pc s = n2w 0x8000002c -> be s = false -> mem_domain s = bootstrapDomain ->
 failed (after (runCode (TAKE 19 tailCode) s) (Inst (Mem Store 6 (Addr 5 tailOffset16)))) =
 failed (runCode (TAKE 19 tailCode) s).
Proof.
 intros Hp Hb Hd; pose proof (tail_site_19 s Hp) as [Ha _]; apply tail_after_store_failed.
 - tail_prefix_expand 19; tail_controls; exact Hb.
 - intros j Hj; rewrite Ha; tail_prefix_expand 19; tail_controls; rewrite Hd;
   apply tail_addresses_domain; [unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto|exact Hj].
 - rewrite Ha; apply tail_addresses_aligned; unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto.
Qed.
Lemma tail_fail_site_21 (s : asm_state 64) :
 pc s = n2w 0x8000002c -> be s = false -> mem_domain s = bootstrapDomain ->
 failed (after (runCode (TAKE 21 tailCode) s) (Inst (Mem Store 6 (Addr 5 tailOffset24)))) =
 failed (runCode (TAKE 21 tailCode) s).
Proof.
 intros Hp Hb Hd; pose proof (tail_site_21 s Hp) as [Ha _]; apply tail_after_store_failed.
 - tail_prefix_expand 21; tail_controls; exact Hb.
 - intros j Hj; rewrite Ha; tail_prefix_expand 21; tail_controls; rewrite Hd;
   apply tail_addresses_domain; [unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto|exact Hj].
 - rewrite Ha; apply tail_addresses_aligned; unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto.
Qed.
Lemma tail_fail_site_23 (s : asm_state 64) :
 pc s = n2w 0x8000002c -> be s = false -> mem_domain s = bootstrapDomain ->
 failed (after (runCode (TAKE 23 tailCode) s) (Inst (Mem Store 6 (Addr 5 tailOffset32)))) =
 failed (runCode (TAKE 23 tailCode) s).
Proof.
 intros Hp Hb Hd; pose proof (tail_site_23 s Hp) as [Ha _]; apply tail_after_store_failed.
 - tail_prefix_expand 23; tail_controls; exact Hb.
 - intros j Hj; rewrite Ha; tail_prefix_expand 23; tail_controls; rewrite Hd;
   apply tail_addresses_domain; [unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto|exact Hj].
 - rewrite Ha; apply tail_addresses_aligned; unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto.
Qed.
Ltac tail_prepare_failures s Hp Hb Hd :=
 let H := fresh "Store3" in pose proof (tail_fail_site_3 s Hp Hb Hd) as H;
 tail_prefix_in 3 H; unfold tailOffset0 in H;
 let H := fresh "Store7" in pose proof (tail_fail_site_7 s Hp Hb Hd) as H;
 tail_prefix_in 7 H; unfold tailOffset0 in H;
 let H := fresh "Store11" in pose proof (tail_fail_site_11 s Hp Hb Hd) as H;
 tail_prefix_in 11 H; unfold tailOffset0 in H;
 let H := fresh "Store15" in pose proof (tail_fail_site_15 s Hp Hb Hd) as H;
 tail_prefix_in 15 H; unfold tailOffset0 in H;
 let H := fresh "Store17" in pose proof (tail_fail_site_17 s Hp Hb Hd) as H;
 tail_prefix_in 17 H; unfold tailOffset8 in H;
 let H := fresh "Store19" in pose proof (tail_fail_site_19 s Hp Hb Hd) as H;
 tail_prefix_in 19 H; unfold tailOffset16 in H;
 let H := fresh "Store21" in pose proof (tail_fail_site_21 s Hp Hb Hd) as H;
 tail_prefix_in 21 H; unfold tailOffset24 in H;
 let H := fresh "Store23" in pose proof (tail_fail_site_23 s Hp Hb Hd) as H;
 tail_prefix_in 23 H; unfold tailOffset32 in H.
Ltac tail_failures := repeat first [rewrite tail_loc_failed | rewrite tail_const_failed |
 rewrite tail_shift_failed | rewrite tail_jump_failed |
 match goal with H : failed (after _ _) = failed _ |- _ => progress rewrite H end].
Theorem tail_success (s : asm_state 64) :
 pc s = n2w 0x8000002c -> be s = false -> mem_domain s = bootstrapDomain ->
 failed (runCode tailCode s) = failed s.
Proof. intros Hp Hb Hd; tail_prepare_failures s Hp Hb Hd; tail_expand; tail_failures; reflexivity. Qed.

Theorem tail_headers_original : tailHeaders =
 [(initDataRam,n2w sourceBase);(initDataRam+8,n2w stackStart);(initDataRam+16,n2w ramEnd)] ++
 combine [sourceBase;sourceBase+8;sourceBase+16;sourceBase+24;sourceBase+32] startupHeaders.
Proof. vm_compute; reflexivity. Qed.
Lemma tail_state_ext (s t : asm_state 64) :
 regs s = regs t -> fp_regs s = fp_regs t -> mem s = mem t ->
 mem_domain s = mem_domain t -> pc s = pc t -> lr s = lr t ->
 align s = align t -> be s = be t -> failed s = failed t -> s = t.
Proof. destruct s,t; cbn; intros; subst; reflexivity. Qed.
Theorem tail_endpoint (s : asm_state 64) :
 pc s = n2w 0x8000002c -> be s = false -> mem_domain s = bootstrapDomain ->
 runCode tailCode s = set_pc (n2w nativePc)
  (set_regs (tailRegisters (regs s)) (set_mem (tailMemory (mem s)) s)).
Proof.
 intros Hp Hb Hd.
 destruct (tail_control s Hp) as [Hpc [Hr [Hfp [Hdomain [Hlr [Hal Hbe]]]]]].
 apply tail_state_ext.
 - exact Hr.
 - exact Hfp.
 - apply tail_memory; assumption.
 - exact Hdomain.
 - exact Hpc.
 - exact Hlr.
 - exact Hal.
 - exact Hbe.
 - exact (tail_success s Hp Hb Hd).
Qed.
Theorem tail_heap_registers (s : asm_state 64) : pc s = n2w 0x8000002c ->
 regs (runCode tailCode s) 10 = n2w nativePc /\
 regs (runCode tailCode s) 11 = n2w sourceBase /\
 regs (runCode tailCode s) 12 = n2w stackStart /\
 regs (runCode tailCode s) 13 = n2w ramEnd.
Proof. intro Hp; rewrite (proj1 (proj2 (tail_control s Hp))); repeat split; reflexivity. Qed.
Theorem tail_headers_bytes (s : asm_state 64) address value j :
 pc s = n2w 0x8000002c -> be s = false -> In (address,value) tailHeaders -> j < 8 ->
 mem (runCode tailCode s) (n2w address+n2w j)%w = (w2w (value >>> (8*j))%w : word 8).
Proof. intros Hp Hb Hi Hj; rewrite tail_memory by assumption; apply tail_memory_headers; assumption. Qed.

Lemma tailWritten_ranges x : tailWritten x ->
 (initDataRam <= w2n x /\ w2n x < initDataRam+24) \/
 (sourceBase <= w2n x /\ w2n x < sourceBase+40).
Proof.
 intros [address [Hin [j [Hj ->]]]].
 unfold tailAddresses,tailHeaders in Hin; cbn [MAP fst In] in Hin.
 repeat destruct Hin as [Hin|Hin]; try contradiction; subst address;
 rewrite word_add_n2w,w2n_n2w; change (dimword 64) with (2^64);
 rewrite N.mod_small by (tail_address_numbers; lia); tail_address_numbers; lia.
Qed.
Theorem tail_memory_frame_outside (s : asm_state 64) x :
 pc s = n2w 0x8000002c -> be s = false ->
 ~ (initDataRam <= w2n x /\ w2n x < initDataRam+24) ->
 ~ (sourceBase <= w2n x /\ w2n x < sourceBase+40) ->
 mem (runCode tailCode s) x = mem s x.
Proof. intros Hp Hb Hram Hsource; apply tail_memory_frame; try assumption.
 intro Hwritten; apply tailWritten_ranges in Hwritten; tauto. Qed.
Lemma tail_put_code address value memory x : In address tailAddresses ->
 initialPc <= w2n x -> w2n x < initialPc+208 ->
 tailPut (n2w address) value memory x = memory x.
Proof.
 intros Hi Hlo Hhi; apply tail_put_out; intros j Hj E.
 assert (Hw : tailWritten x) by (exists address; split; [exact Hi|exists j; auto]).
 apply tailWritten_ranges in Hw; cbv [initialPc initDataRam sourceBase] in *; lia.
Qed.

Lemma tail_bytes_transport (bytes : list (word 8)) (p : word 64) m1 m2 domain :
 (forall j, j < LENGTH bytes -> m1 (p+n2w j)%w = m2 (p+n2w j)%w) ->
 bytes_in_memory p bytes m2 domain -> bytes_in_memory p bytes m1 domain.
Proof.
 revert p; induction bytes as [|byte rest IH]; intros p Hm Hb; cbn [bytes_in_memory] in *.
 - constructor.
 - destruct Hb as [Hbyte [Hd Hrest]]; apply conj.
   + specialize (Hm 0 ltac:(cbn [LENGTH]; lia)); rewrite (proj1 WORD_ADD_0) in Hm; rewrite Hm; exact Hbyte.
   + apply conj; [exact Hd|]. apply IH; [|exact Hrest].
     intros j Hj; rewrite bootstrap_word_advance; apply Hm; cbn [LENGTH]; lia.
Qed.
Lemma tail_checked_bytes (s : asm_state 64) address i :
 In (address,i) bootstrapBlocks -> pc s = n2w address ->
 mem_domain s = bootstrapDomain ->
 (forall x, initialPc <= w2n x -> w2n x < initialPc+208 -> mem s x = romMemory x) ->
 bytes_in_memory (pc s) (riscv_target.riscv_enc i) (mem s) (mem_domain s).
Proof.
 intros Hi Hp Hd Hm; rewrite Hp,Hd; apply (tail_bytes_transport _ _ _ romMemory).
 - intros j Hj; apply Hm; rewrite word_add_n2w,w2n_n2w;
   change (dimword 64) with (2^64);
   pose proof (bootstrap_block_bounds (address,i) Hi) as [Hlo Hhi]; cbn [fst snd] in Hlo,Hhi;
   rewrite N.mod_small by (unfold initialPc in *; lia); lia.
 - exact (block_bytes (address,i) Hi).
Qed.

Ltac tail_prepare_addresses s Hp :=
 let Ha := fresh "Address3" in let Hv := fresh "Value3" in
 pose proof (tail_site_3 s Hp) as [Ha Hv];
 tail_prefix_in 3 Ha; unfold tailOffset0 in Ha;
 let Ha := fresh "Address7" in let Hv := fresh "Value7" in
 pose proof (tail_site_7 s Hp) as [Ha Hv];
 tail_prefix_in 7 Ha; unfold tailOffset0 in Ha;
 let Ha := fresh "Address11" in let Hv := fresh "Value11" in
 pose proof (tail_site_11 s Hp) as [Ha Hv];
 tail_prefix_in 11 Ha; unfold tailOffset0 in Ha;
 let Ha := fresh "Address15" in let Hv := fresh "Value15" in
 pose proof (tail_site_15 s Hp) as [Ha Hv];
 tail_prefix_in 15 Ha; unfold tailOffset0 in Ha;
 let Ha := fresh "Address17" in let Hv := fresh "Value17" in
 pose proof (tail_site_17 s Hp) as [Ha Hv];
 tail_prefix_in 17 Ha; unfold tailOffset8 in Ha;
 let Ha := fresh "Address19" in let Hv := fresh "Value19" in
 pose proof (tail_site_19 s Hp) as [Ha Hv];
 tail_prefix_in 19 Ha; unfold tailOffset16 in Ha;
 let Ha := fresh "Address21" in let Hv := fresh "Value21" in
 pose proof (tail_site_21 s Hp) as [Ha Hv];
 tail_prefix_in 21 Ha; unfold tailOffset24 in Ha;
 let Ha := fresh "Address23" in let Hv := fresh "Value23" in
 pose proof (tail_site_23 s Hp) as [Ha Hv];
 tail_prefix_in 23 Ha; unfold tailOffset32 in Ha.
Ltac tail_memories Hb := repeat first [rewrite tail_loc_mem | rewrite tail_const_mem |
 rewrite tail_shift_mem | rewrite tail_jump_mem |
 rewrite tail_after_store_memory by (tail_controls; exact Hb)].
Ltac tail_address_rewrites := repeat match goal with
 H : (regs _ 5 + _) %w = n2w _ |- _ => progress rewrite H end.
Ltac tail_check_block address Hp Hb Hd Hl Ha Hf Hcode :=
 apply checked_step;
 [ apply (tail_checked_bytes _ address);
   [ vm_compute; tauto |
     tail_pc_regs; rewrite Hp; vm_compute; reflexivity |
     tail_controls; exact Hd |
     let x := fresh "CodeAddress" in let Hlo := fresh "CodeLo" in let Hhi := fresh "CodeHi" in
     intros x Hlo Hhi; tail_memories Hb; tail_address_rewrites;
     repeat rewrite tail_put_code by
      (first [unfold tailAddresses,tailHeaders; cbn [MAP fst In]; tauto | exact Hlo | exact Hhi]);
     apply Hcode; assumption ] |
   tail_controls; exact Hl |
   tail_controls; exact Hb |
   tail_controls; exact Ha |
   tail_failures; rewrite Hf; intro; discriminate |
   vm_compute; reflexivity ].

(** Code agreement is only over the actual 208-byte bootstrap ROM. All other
    incoming memory is unrestricted, including the prior copy and host overlay. *)
Theorem tail_checked (s : asm_state 64) :
 pc s = n2w 0x8000002c -> be s = false -> mem_domain s = bootstrapDomain ->
 lr s = 1 -> align s = 2 -> failed s = false ->
 (forall x, initialPc <= w2n x -> w2n x < initialPc+208 -> mem s x = romMemory x) ->
 Checked tailCode s.
Proof.
 intros Hp Hb Hd Hl Ha Hf Hcode.
 tail_prepare_addresses s Hp; tail_prepare_failures s Hp Hb Hd.
 rewrite tail_code_list; cbn [tailInstructions Checked].
 split; [tail_check_block 0x8000002c Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x80000034 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x80000038 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x8000003c Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x80000040 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x80000048 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x8000004c Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x80000050 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x80000054 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x8000005c Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x80000060 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x80000064 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x80000068 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x8000006c Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x80000070 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x80000078 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x8000007c Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x80000084 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x80000088 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x80000090 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x80000094 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x8000009c Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x800000a0 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x800000a8 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x800000ac Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x800000b0 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x800000b4 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x800000b8 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x800000bc Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x800000c0 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x800000c4 Hp Hb Hd Hl Ha Hf Hcode|].
 split; [tail_check_block 0x800000cc Hp Hb Hd Hl Ha Hf Hcode|].
 constructor.
Qed.
Theorem tail_checked_trace (s : asm_state 64) :
 pc s = n2w 0x8000002c -> be s = false -> mem_domain s = bootstrapDomain ->
 lr s = 1 -> align s = 2 -> failed s = false ->
 (forall x, initialPc <= w2n x -> w2n x < initialPc+208 -> mem s x = romMemory x) ->
 RTC (fun before after => exists i, asm_step riscv_target.riscv_config before i after)
 s (set_pc (n2w nativePc) (set_regs (tailRegisters (regs s)) (set_mem (tailMemory (mem s)) s))).
Proof.
 intros Hp Hb Hd Hl Ha Hf Hcode; rewrite <- tail_endpoint by assumption.
 apply checked_trace; apply tail_checked; assumption.
Qed.
