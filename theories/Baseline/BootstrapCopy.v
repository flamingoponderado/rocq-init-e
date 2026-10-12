(** Original BootstrapCopy.lean: byte-exact LD/SD copying, with alignment
    and domain success obligations kept separate from unconditional memory facts. *)
From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.n_bit Require Import words byte alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.combin Require Import combin.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import inst.
From Galette.cakeml.compiler.encoders.riscv.proofs Require riscv_targetProof.
From InitE.Baseline Require Import BootstrapMemoryControl.
Import ByteBits.
Open Scope N_scope.
Definition copyWord (s : asm_state 64) : asm_state 64 :=
 mem_store 8 28 (Addr 6 (n2w 0)) (mem_load 8 28 (Addr 5 (n2w 0)) s).
Theorem read_selected_byte (s : asm_state 64) (p : word 64) j :
 be s = false -> j < 8 ->
 (w2w ((fst (read_mem_word p 8 s)) >>> (8*j))%w : word 8) = mem s (p+n2w j)%w.
Proof.
 intros Hbe Hj; apply word_testbit_eq; intros bit Hbit.
 change (bit < 8) in Hbit.
 rewrite testbit_w2w,testbit_lsr,read_mem_word_bits.
 change (dimindex 8) with 8; change (dimindex 64) with 64.
 assert (A : (bit <? 8) = true) by (apply N.ltb_lt; exact Hbit).
 assert (B : (bit+8*j <? 64) = true) by (apply N.ltb_lt; nia).
 change (8*8) with 64.
 rewrite A,B; cbn [andb].
 replace (bit+8*j) with (bit+j*8) by nia.
 rewrite N.div_add by discriminate.
 rewrite N.Div0.mod_add.
 rewrite N.div_small,N.mod_small by exact Hbit.
 rewrite N.add_0_l.
 unfold offs; rewrite Hbe; reflexivity.
Qed.

Theorem load_frame (s : asm_state 64) : be s = false ->
 let loaded := mem_load 8 28 (Addr 5 (n2w 0)) s in
 mem loaded = mem s /\ be loaded = false /\
 regs loaded 6 = regs s 6 /\
 regs loaded 28 = fst (read_mem_word (regs s 5) 8 s).
Proof.
 intro Hbe; cbv zeta; unfold mem_load,addr,read_reg.
 rewrite (proj1 WORD_ADD_0),Hbe.
 pose proof (riscv_targetProof.rmw_facts 8 (regs s 5) s Hbe) as R.
 pose proof (SND_read_mem_word_consts 8 (regs s 5) s) as C.
 destruct (read_mem_word (regs s 5) 8 s) as [v post] eqn:E.
 cbn [fst snd] in R,C.
 destruct R as [_ [Hr [Hm [_ _]]]]. destruct C as [Hb _].
 cbn [assert set_failed upd_reg set_regs mem be regs].
 rewrite Hr,Hm,Hb,Hbe.
 split; [reflexivity|]. split; [reflexivity|].
 split; unfold UPDATE; reflexivity.
Qed.


Lemma assert_memory {a} b (s : asm_state a) : mem (assert b s) = mem s.
Proof. reflexivity. Qed.
Theorem store_selected_byte (s : asm_state 64) r base j :
 be s = false -> j < 8 ->
 mem (mem_store 8 r (Addr base (n2w 0)) s) (regs s base+n2w j)%w =
 (w2w (regs s r >>> (8*j))%w : word 8).
Proof.
 intros Hb Hj; unfold mem_store,addr,read_reg.
 rewrite (proj1 WORD_ADD_0),Hb.
 rewrite assert_memory.
 replace (regs s base+n2w j)%w with (offs (be s) (regs s base) j).
 2:{ unfold offs; rewrite Hb; reflexivity. }
 apply write_mem_word_mem_in; [vm_compute; discriminate|exact Hj].
Qed.
Theorem store_byte_frame (s : asm_state 64) r base x : be s = false ->
 (forall j, j < 8 -> x <> (regs s base+n2w j)%w) ->
 mem (mem_store 8 r (Addr base (n2w 0)) s) x = mem s x.
Proof.
 intros Hb Houtside; unfold mem_store,addr,read_reg.
 rewrite (proj1 WORD_ADD_0),Hb.
 rewrite assert_memory.
 apply write_mem_word_mem_out.
 intros j Hj; unfold offs; rewrite Hb; apply Houtside; exact Hj.
Qed.
Theorem copyWord_selected (s : asm_state 64) j : be s = false -> j < 8 ->
 mem (copyWord s) (regs s 6+n2w j)%w = mem s (regs s 5+n2w j)%w.
Proof.
 intros Hbe Hj; pose proof (load_frame s Hbe) as H.
 set (loaded := mem_load 8 28 (Addr 5 (n2w 0)) s) in *.
 destruct H as [Hm [Hb [Hr Hv]]].
 unfold copyWord; fold loaded.
 rewrite <- Hr at 1.
 rewrite store_selected_byte by assumption.
 rewrite Hv; apply read_selected_byte; assumption.
Qed.
Theorem copyWord_frame (s : asm_state 64) x : be s = false ->
 (forall j, j < 8 -> x <> (regs s 6+n2w j)%w) ->
 mem (copyWord s) x = mem s x.
Proof.
 intros Hbe Houtside; pose proof (load_frame s Hbe) as H.
 set (loaded := mem_load 8 28 (Addr 5 (n2w 0)) s) in *.
 destruct H as [Hm [Hb [Hr Hv]]].
 unfold copyWord; fold loaded.
 rewrite store_byte_frame; [exact (f_equal (fun m => m x) Hm)|exact Hb|].
 intros j Hj; rewrite Hr; apply Houtside; exact Hj.
Qed.

Lemma assert_failure {a} b (s : asm_state a) :
 failed (assert b s) = negb b || failed s.
Proof. reflexivity. Qed.
Lemma upd_reg_failure {a} r value (s : asm_state a) :
 failed (upd_reg r value s) = failed s.
Proof. reflexivity. Qed.
Theorem load_success_failure (s : asm_state 64) r base : be s = false ->
 (forall j, j < 8 -> mem_domain s (regs s base+n2w j)%w) ->
 aligned 3 (regs s base) = true ->
 failed (mem_load 8 r (Addr base (n2w 0)) s) = failed s.
Proof.
 intros Hb Hd Ha; unfold mem_load,addr,read_reg.
 rewrite (proj1 WORD_ADD_0),Hb.
 assert (Hs : snd (read_mem_word (regs s base) 8 s) = s).
 { apply read_mem_word_snd; intros j Hj; unfold offs; rewrite Hb; apply Hd; exact Hj. }
 rewrite (surjective_pairing (read_mem_word (regs s base) 8 s)),Hs.
 cbn [fst snd]. change (LOG2 8) with 3.
 rewrite Ha,assert_failure,upd_reg_failure; reflexivity.
Qed.
Theorem store_success_failure (s : asm_state 64) r base : be s = false ->
 (forall j, j < 8 -> mem_domain s (regs s base+n2w j)%w) ->
 aligned 3 (regs s base) = true ->
 failed (mem_store 8 r (Addr base (n2w 0)) s) = failed s.
Proof.
 intros Hb Hd Ha; unfold mem_store,addr,read_reg.
 rewrite (proj1 WORD_ADD_0),Hb.
 change (LOG2 8) with 3.
 rewrite Ha,assert_failure; cbn [negb orb].
 apply write_mem_word_failed; intros j Hj; unfold offs; rewrite Hb; apply Hd; exact Hj.
Qed.
Theorem copyWord_success (s : asm_state 64) :
 be s = false -> failed s = false ->
 (forall j, j < 8 -> mem_domain s (regs s 5+n2w j)%w) ->
 (forall j, j < 8 -> mem_domain s (regs s 6+n2w j)%w) ->
 aligned 3 (regs s 5) = true -> aligned 3 (regs s 6) = true ->
 failed (copyWord s) = false.
Proof.
 intros Hb Hf Hsource Hdest Has Had; pose proof (load_frame s Hb) as H.
 set (loaded := mem_load 8 28 (Addr 5 (n2w 0)) s) in *.
 destruct H as [Hm [Hbl [Hr Hv]]].
 pose proof (mem_load_consts 8 28 (Addr 5 (n2w 0)) s) as [_ [_ [_ Hd]]].
 fold loaded in Hd.
 unfold copyWord; fold loaded.
 rewrite store_success_failure.
 - unfold loaded; rewrite load_success_failure; assumption.
 - exact Hbl.
 - intros j Hj; rewrite Hd,Hr; apply Hdest; exact Hj.
 - rewrite Hr; exact Had.
Qed.

Theorem copyWord_registers (s : asm_state 64) : be s = false ->
 regs (copyWord s) = UPDATE 28 (fst (read_mem_word (regs s 5) 8 s)) (regs s).
Proof.
 intro Hb; unfold copyWord; rewrite mem_store_registers,mem_load_registers by exact Hb.
 unfold addr,read_reg; rewrite (proj1 WORD_ADD_0); reflexivity.
Qed.

Theorem copyWord_other_register (s : asm_state 64) r : be s = false -> r <> 28 ->
 regs (copyWord s) r = regs s r.
Proof.
 intros Hb Hr; rewrite copyWord_registers by exact Hb.
 unfold UPDATE; destruct (decide (28=r)) as [E|E]; [congruence|reflexivity].
Qed.

Theorem copyWord_endian s : be (copyWord s) = be s.
Proof.
 unfold copyWord; rewrite (proj1 (mem_store_consts 8 28 (Addr 6 (n2w 0)) _)).
 exact (proj1 (mem_load_consts 8 28 (Addr 5 (n2w 0)) s)).
Qed.
Theorem copyWord_domain s : mem_domain (copyWord s) = mem_domain s.
Proof.
 unfold copyWord; rewrite (proj2 (proj2 (proj2 (mem_store_consts 8 28 (Addr 6 (n2w 0)) _)))).
 exact (proj2 (proj2 (proj2 (mem_load_consts 8 28 (Addr 5 (n2w 0)) s)))).
Qed.
Theorem copyWord_link s : lr (copyWord s) = lr s.
Proof.
 unfold copyWord; rewrite (proj1 (proj2 (mem_store_consts 8 28 (Addr 6 (n2w 0)) _))).
 exact (proj1 (proj2 (mem_load_consts 8 28 (Addr 5 (n2w 0)) s))).
Qed.
Theorem copyWord_alignment s : align (copyWord s) = align s.
Proof.
 unfold copyWord; rewrite (proj1 (proj2 (proj2 (mem_store_consts 8 28 (Addr 6 (n2w 0)) _)))).
 exact (proj1 (proj2 (proj2 (mem_load_consts 8 28 (Addr 5 (n2w 0)) s)))).
Qed.
