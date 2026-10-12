(** Memory operations preserve bootstrap control fields. These lemmas keep
    recursively asserted state records abstract in subsequent loop proofs. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.combin Require Import combin.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import inst.
From Galette.cakeml.compiler.encoders.riscv.proofs Require riscv_targetProof.
Open Scope N_scope.
Lemma asm_assert_registers {a} b (s : asm_state a) : regs (assert b s) = regs s.
Proof. reflexivity. Qed.
Theorem read_word_control n : forall (ad : word 64) s,
 pc (snd (read_mem_word ad n s)) = pc s /\
 fp_regs (snd (read_mem_word ad n s)) = fp_regs s.
Proof.
 induction n as [|n IH] using N.peano_ind; intros ad s.
 - split; reflexivity.
 - rewrite (proj2 (read_mem_word_def ad n s)).
   pose proof (IH (if be s then (ad-n2w 1)%w else (ad+n2w 1)%w) s) as H.
   destruct (read_mem_word (if be s then (ad-n2w 1)%w else (ad+n2w 1)%w) n s)
    as [value post] eqn:E.
   cbn [snd] in H.
   cbn [snd assert set_failed pc fp_regs]; exact H.
Qed.
Theorem write_word_control n : forall (ad value : word 64) s,
 pc (write_mem_word ad n value s) = pc s /\
 fp_regs (write_mem_word ad n value s) = fp_regs s.
Proof.
 induction n as [|n IH] using N.peano_ind; intros ad value s.
 - split; reflexivity.
 - rewrite (proj2 (write_mem_word_def ad n value s)).
   cbv zeta; cbn [assert set_failed upd_mem set_mem pc fp_regs].
   apply IH.
Qed.
Theorem mem_store_registers n r (address : asm.addr 64) s :
 regs (mem_store n r address s) = regs s.
Proof. unfold mem_store; cbv zeta; rewrite asm_assert_registers; apply write_mem_word_regs. Qed.
Theorem mem_load_registers n r (address : asm.addr 64) s : be s = false ->
 regs (mem_load n r address s) =
 UPDATE r (fst (read_mem_word (addr address s) n s)) (regs s).
Proof.
 intro Hb; unfold mem_load; rewrite Hb.
 pose proof (riscv_targetProof.rmw_facts n (addr address s) s Hb) as H.
 destruct (read_mem_word (addr address s) n s) as [value post] eqn:E.
 cbn [fst snd] in H; destruct H as [_ [Hr _]].
 rewrite asm_assert_registers; cbn [upd_reg set_regs regs]; rewrite Hr; reflexivity.
Qed.
Theorem mem_load_control n r (address : asm.addr 64) s :
 pc (mem_load n r address s) = pc s /\ fp_regs (mem_load n r address s) = fp_regs s.
Proof.
 unfold mem_load; cbv zeta.
 pose proof (read_word_control n (if be s then (addr address s+n2w (n-1))%w else addr address s) s) as H.
 destruct (read_mem_word (if be s then (addr address s+n2w (n-1))%w else addr address s) n s)
 as [value post] eqn:E.
 cbn [snd] in H.
 cbn [assert set_failed upd_reg set_regs pc fp_regs]; exact H.
Qed.
Theorem mem_store_control n r (address : asm.addr 64) s :
 pc (mem_store n r address s) = pc s /\ fp_regs (mem_store n r address s) = fp_regs s.
Proof.
 unfold mem_store; cbv zeta.
 cbn [assert set_failed pc fp_regs]. apply write_word_control.
Qed.

Lemma upd_pc_endian {a} p (s : asm_state a) : be (upd_pc p s) = be s.
Proof. reflexivity. Qed.
Lemma upd_pc_domain {a} p (s : asm_state a) : mem_domain (upd_pc p s) = mem_domain s.
Proof. reflexivity. Qed.
Lemma assert_upd_pc {a} b p (s : asm_state a) :
 assert b (upd_pc p s) = upd_pc p (assert b s).
Proof. reflexivity. Qed.
Lemma upd_reg_upd_pc {a} r value p (s : asm_state a) :
 upd_reg r value (upd_pc p s) = upd_pc p (upd_reg r value s).
Proof. reflexivity. Qed.
Lemma upd_mem_upd_pc {a} address value p (s : asm_state a) :
 upd_mem address value (upd_pc p s) = upd_pc p (upd_mem address value s).
Proof. reflexivity. Qed.
Lemma addr_upd_pc (address : asm.addr 64) p s : addr address (upd_pc p s) = addr address s.
Proof. destruct address; reflexivity. Qed.
Theorem read_word_upd_pc n : forall (ad p : word 64) s,
 read_mem_word ad n (upd_pc p s) =
 let '(value,post) := read_mem_word ad n s in (value,upd_pc p post).
Proof.
 induction n as [|n IH] using N.peano_ind; intros ad p s.
 - reflexivity.
 - rewrite (proj2 (read_mem_word_def ad n (upd_pc p s))).
   rewrite (proj2 (read_mem_word_def ad n s)),upd_pc_endian,IH.
   destruct (read_mem_word (if be s then (ad-n2w 1)%w else (ad+n2w 1)%w) n s)
   as [value post] eqn:E.
   cbn [fst snd]; rewrite upd_pc_domain,assert_upd_pc.
   unfold read_mem; cbn [upd_pc set_pc mem]; reflexivity.
Qed.
Theorem write_word_upd_pc n : forall (ad value p : word 64) s,
 write_mem_word ad n value (upd_pc p s) = upd_pc p (write_mem_word ad n value s).
Proof.
 induction n as [|n IH] using N.peano_ind; intros ad value p s.
 - reflexivity.
 - rewrite (proj2 (write_mem_word_def ad n value (upd_pc p s))).
   rewrite (proj2 (write_mem_word_def ad n value s)),upd_pc_endian,IH.
   cbv zeta; rewrite upd_pc_domain,upd_mem_upd_pc,assert_upd_pc; reflexivity.
Qed.
Theorem mem_load_upd_pc n r (address : asm.addr 64) p s :
 mem_load n r address (upd_pc p s) = upd_pc p (mem_load n r address s).
Proof.
 unfold mem_load; rewrite addr_upd_pc,upd_pc_endian,read_word_upd_pc.
 destruct (read_mem_word (if be s then (addr address s+n2w (n-1))%w else addr address s) n s)
 as [value post] eqn:E.
 rewrite upd_reg_upd_pc,assert_upd_pc; reflexivity.
Qed.
Theorem mem_store_upd_pc n r (address : asm.addr 64) p s :
 mem_store n r address (upd_pc p s) = upd_pc p (mem_store n r address s).
Proof.
 unfold mem_store; rewrite addr_upd_pc,upd_pc_endian.
 change (read_reg r (upd_pc p s)) with (read_reg r s).
 rewrite write_word_upd_pc,assert_upd_pc; reflexivity.
Qed.
