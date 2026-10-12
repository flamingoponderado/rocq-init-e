(** The actual checked bootstrap endpoint has the original installed memory.
    Original BootstrapMemory.lean: installation is the proved conclusion. *)
From Galette Require Import Base.
From Stdlib Require Import NArith Lia Bool.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem.
From InitE.Guest Require Import Basic Bookkeeping.
From InitE.InitE Require Import Parameters BaselineArtifactLayout.
From InitE.Baseline Require Import Artifacts BootstrapMemory BootstrapSteps BootstrapTail
 BootstrapCopyInvariant BootstrapCopyChecked.
Open Scope N_scope.
Local Opaque Artifacts.code romMemory after copyState.

Lemma installed_word_byte (value : word 64) offset :
 wordByte value offset = (w2w (value >>> (8*offset))%w : word 8).
Proof. unfold wordByte,w2w; rewrite w2n_lsr; reflexivity. Qed.
Lemma installed_word_decompose (a : word 64) base : base <= w2n a ->
 a = (n2w (base+8*((w2n a-base)/8))+n2w ((w2n a-base) mod 8))%w.
Proof.
 intro Hbase; rewrite <- (n2w_w2n a) at 1; rewrite word_add_n2w.
 f_equal; pose proof (N.div_mod (w2n a-base) 8 ltac:(discriminate)); lia.
Qed.
Lemma installed_guard_range base limit (a : word 64) :
 (base <=? w2n a) && (w2n a <? limit) = true <-> base <= w2n a /\ w2n a < limit.
Proof. rewrite andb_true_iff,N.leb_le,N.ltb_lt; reflexivity. Qed.
Lemma installed_guard_outside base limit (a : word 64) :
 (base <=? w2n a) && (w2n a <? limit) = false -> ~ (base <= w2n a /\ w2n a < limit).
Proof. intros Hfalse Hin; apply (proj2 (installed_guard_range base limit a)) in Hin; congruence. Qed.
Lemma installed_source_header i : i < 5 ->
 In (sourceBase+8*i,nthN i startupHeaders (n2w 0)) tailHeaders.
Proof.
 intro Hi; assert (E : i=0 \/ i=1 \/ i=2 \/ i=3 \/ i=4) by lia.
 repeat destruct E as [E|E]; subst i; vm_compute; tauto.
Qed.
Lemma installed_init_header i : i < 3 ->
 In (initDataRam+8*i,nthN i [n2w sourceBase;n2w stackStart;n2w ramEnd] (n2w 0)) tailHeaders.
Proof.
 intro Hi; assert (E : i=0 \/ i=1 \/ i=2) by lia.
 repeat destruct E as [E|E]; subst i; vm_compute; tauto.
Qed.

Theorem bootstrap_endpoint_headers address value j :
 In (address,value) tailHeaders -> j < 8 ->
 mem bootstrapEndpoint (n2w address+n2w j)%w = (w2w (value >>> (8*j))%w : word 8).
Proof.
 intros Hi Hj; pose proof (copy_control_all 4617 ltac:(lia)) as Hcopy.
 unfold bootstrapEndpoint; apply tail_headers_bytes.
 - exact (copy_pc 4617 (copyState 4617) Hcopy).
 - exact (copy_endian 4617 (copyState 4617) Hcopy).
 - exact Hi.
 - exact Hj.
Qed.
Theorem bootstrap_endpoint_tail_frame a :
 ~ (initDataRam <= w2n a /\ w2n a < initDataRam+24) ->
 ~ (sourceBase <= w2n a /\ w2n a < sourceBase+40) ->
 mem bootstrapEndpoint a = mem (copyState 4617) a.
Proof.
 intros Hinit Hsource; pose proof (copy_control_all 4617 ltac:(lia)) as Hcopy.
 unfold bootstrapEndpoint; apply tail_memory_frame_outside.
 - exact (copy_pc 4617 (copyState 4617) Hcopy).
 - exact (copy_endian 4617 (copyState 4617) Hcopy).
 - exact Hinit.
 - exact Hsource.
Qed.

Local Opaque bootstrapEndpoint mem.
Theorem bootstrap_endpoint_memory : mem bootstrapEndpoint = installedMemory.
Proof.
 apply functional_extensionality; intro a; unfold installedMemory.
 destruct ((sourceBase <=? w2n a) && (w2n a <? sourceBase+40)) eqn:Hsource.
 - apply (proj1 (installed_guard_range _ _ a)) in Hsource as [Hlo Hhi].
   assert (Hi : (w2n a-sourceBase)/8 < 5) by (apply N.Div0.div_lt_upper_bound; lia).
   assert (Hj : (w2n a-sourceBase) mod 8 < 8) by (apply N.mod_lt; discriminate).
   exact (eq_trans (f_equal (mem bootstrapEndpoint) (installed_word_decompose a sourceBase Hlo))
    (eq_trans (bootstrap_endpoint_headers _ _ _ (installed_source_header _ Hi) Hj)
     (eq_sym (installed_word_byte _ _)))).
 - pose proof (installed_guard_outside _ _ a Hsource) as HoutSource.
   destruct ((initDataRam <=? w2n a) && (w2n a <? initDataRam+24)) eqn:Hinit.
   + apply (proj1 (installed_guard_range _ _ a)) in Hinit as [Hlo Hhi].
     assert (Hi : (w2n a-initDataRam)/8 < 3) by (apply N.Div0.div_lt_upper_bound; lia).
     assert (Hj : (w2n a-initDataRam) mod 8 < 8) by (apply N.mod_lt; discriminate).
     exact (eq_trans (f_equal (mem bootstrapEndpoint) (installed_word_decompose a initDataRam Hlo))
      (eq_trans (bootstrap_endpoint_headers _ _ _ (installed_init_header _ Hi) Hj)
       (eq_sym (installed_word_byte _ _)))).
   + pose proof (installed_guard_outside _ _ a Hinit) as HoutInit.
     destruct ((initDataRam+24 <=? w2n a) && (w2n a <? initDataEnd)) eqn:Hbitmap.
     * apply (proj1 (installed_guard_range _ _ a)) in Hbitmap as [Hlo Hhi].
       rewrite bootstrap_endpoint_tail_frame by (exact HoutInit || exact HoutSource).
       assert (Ha : a = n2w (initDataRam+(w2n a-initDataRam))).
       { rewrite <- (n2w_w2n a) at 1; f_equal; lia. }
       assert (Ho : w2n a-initDataRam < 8*4617) by (cbv [initDataEnd bitmapWordCount] in Hhi; lia).
       eapply eq_trans.
       -- exact (f_equal (mem (copyState 4617)) Ha).
       -- rewrite (copy_loop_bytes_endpoint _ Ho).
          replace (initDataRom+(w2n a-initDataRam)) with (initDataRom+w2n a-initDataRam) by lia; reflexivity.
     * pose proof (installed_guard_outside _ _ a Hbitmap) as HoutBitmap.
       rewrite bootstrap_endpoint_tail_frame by (exact HoutInit || exact HoutSource).
       apply copy_loop_frame_endpoint; intro Hin; apply HoutBitmap; destruct Hin as [Hlo Hhi]; split; lia.
Qed.

Local Transparent bootstrapEndpoint mem.
Theorem bootstrap_endpoint_pc : pc bootstrapEndpoint = n2w nativePc.
Proof.
 pose proof (copy_control_all 4617 ltac:(lia)) as Hcopy; unfold bootstrapEndpoint.
 exact (proj1 (tail_control (copyState 4617) (copy_pc 4617 (copyState 4617) Hcopy))).
Qed.
Theorem bootstrap_endpoint_heap_registers :
 regs bootstrapEndpoint 10 = n2w nativePc /\ regs bootstrapEndpoint 11 = n2w sourceBase /\
 regs bootstrapEndpoint 12 = n2w stackStart /\ regs bootstrapEndpoint 13 = n2w ramEnd.
Proof.
 pose proof (copy_control_all 4617 ltac:(lia)) as Hcopy; unfold bootstrapEndpoint.
 exact (tail_heap_registers (copyState 4617) (copy_pc 4617 (copyState 4617) Hcopy)).
Qed.
Theorem bootstrap_endpoint_controls :
 mem_domain bootstrapEndpoint = bootstrapDomain /\ lr bootstrapEndpoint = 1 /\
 align bootstrapEndpoint = 2 /\ be bootstrapEndpoint = false /\ failed bootstrapEndpoint = false.
Proof.
 pose proof (copy_control_all 4617 ltac:(lia)) as Hcopy.
 pose proof (copy_pc 4617 (copyState 4617) Hcopy) as Hp.
 pose proof (copy_endian 4617 (copyState 4617) Hcopy) as Hb.
 pose proof (copy_domain 4617 (copyState 4617) Hcopy) as Hd.
 destruct (tail_control (copyState 4617) Hp) as [_ [_ [_ [Hdomain [Hlr [Halign Hbe]]]]]].
 unfold bootstrapEndpoint; apply conj.
 - rewrite Hdomain; exact Hd.
 - apply conj.
   + rewrite Hlr; exact (copy_link 4617 (copyState 4617) Hcopy).
   + apply conj.
     * rewrite Halign; exact (copy_alignment 4617 (copyState 4617) Hcopy).
     * apply conj.
       -- rewrite Hbe; exact Hb.
       -- rewrite (tail_success (copyState 4617) Hp Hb Hd); exact (copy_failed 4617 (copyState 4617) Hcopy).
Qed.
