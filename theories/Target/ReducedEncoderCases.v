(** Assembly path proofs adapted from pinned Galette riscv_targetProof,
    commit6eab85e03c934eae714ecf5eb02061b55f2843c1, onto reduced enc_sim. *)
From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.n_bit Require Import words bitstring alignment.
From Galette.HOL.src.n_bit.words Require Import fcp_defs.
From Galette.HOL.src.n_bit.words Require lemmas.
From Galette.HOL.src.integer Require Import integer_word.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.examples.machine_code.hoare_triple Require set_sep.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.HOL.examples.l3_machine_code.riscv.model Require Import riscv.
From Galette.HOL.examples.l3_machine_code.riscv.step Require Import riscv_step.
From Galette.cakeml.compiler.encoders.riscv Require Import riscv_target.
Open Scope N_scope.
From Galette.cakeml.compiler.encoders.riscv.proofs Require Import riscv_targetProof.
From InitE.Target Require Import Configuration StateEmbedding StateAgreement TargetProperties ReducedEncoderPaths.
Definition riscv_target := Configuration.riscvTarget.
Definition A0_of s ms := riscv_targetProof.A0_of s (embedriscv_state ms).
Definition enc_goal := reduced_enc_goal.
Definition enc_sim := reduced_enc_sim.
Lemma hyp_facts s1 i s2 ms :
  asm_step riscv_config s1 i s2 -> target_state_rel riscv_target s1 ms ->
  aligned 2 s1.(pc) = true /\ s1.(be) = false /\
  asm i (word_add s1.(pc) (n2w (LENGTH (riscv_enc i)))) s1 = s2 /\ s2.(failed) = false /\
  asm_ok i riscv_config = true /\
  (forall r, r < 32 -> r <> 0 -> r <> 2 -> r <> 3 -> r <> 4 -> r <> 31 -> riscv_targetProof.gregs (embedriscv_state ms) (n2w r) = s1.(regs) r).
Proof.
 intros Hs Hr; apply (riscv_targetProof.hyp_facts s1 i s2 (embedriscv_state ms) Hs).
 apply (proj1 (asm_relation_embedding s1 ms)); exact Hr.
Qed.
Lemma sim_alu s1 ii s2 ms l :
  asm_step riscv_config s1 (Inst ii) s2 -> target_state_rel riscv_target s1 ms ->
  riscv_ast (Inst ii) = l -> l <> [] -> forallb is_alu l = true ->
  s2.(mem) = s1.(mem) ->
  (forall r, r < 32 -> r <> 0 -> r <> 2 -> r <> 3 -> r <> 4 -> r <> 31 ->
     aregs (arun (A0_of s1 ms) l) (n2w r) = s2.(regs) r) ->
  enc_goal s1 (Inst ii) s2 ms.
Proof.
  intros Hs Hr Hl Hne Hall Hm Hregs. unfold A0_of in *.
  destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & _ & Hasm & _).
  pose proof Hs as (Hb & _).
  destruct (alu_run s1 (Inst ii) s1.(mem_domain) l (A0_of s1 ms) Hal Hl Hne Hall Hb eq_refl eq_refl)
    as (Hrun & Hpc & Hmem).
  unfold A0_of in Hpc,Hmem,Hrun.
  unfold A0_of in *.
  apply (enc_sim s1 (Inst ii) s2 ms l Hs Hr Hne Hrun).
  split; [|split].
  - rewrite Hpc, <- Hasm. reflexivity.
  - intros a Ha. rewrite Hmem, Hm. reflexivity.
  - intros r Hr0 Hav. apply avoid_iff in Hav as (H0 & H2 & H3 & H4 & H31). apply Hregs; assumption.
Qed.

Ltac eqb_simp :=
  repeat match goal with
  | |- context [N.eqb ?a ?a] => rewrite (N.eqb_refl a)
  | |- context [N.eqb ?a ?b] => rewrite (proj2 (N.eqb_neq a b)) by lia
  | |- context [N.eqb ?a ?b] => rewrite (proj2 (N.eqb_eq a b)) by lia
  end; cbv iota.

Ltac regs_simp :=
  repeat (first [ match goal with |- context [rreg ?g (n2w 0)] => rewrite (rreg_0 g) end
                | match goal with |- context [wreg (n2w 0) ?v ?g] => rewrite (wreg_0 v g) end
                | match goal with |- context [rreg ?g (n2w ?r)] => rewrite (rreg_n2w g r) by lia end
                | match goal with |- context [wreg (n2w ?r) ?v ?g (n2w ?x)] => rewrite (wreg_n2w r v g x) by lia end ];
          eqb_simp).

Lemma sim_skip s1 s2 ms :
  asm_step riscv_config s1 (Inst asm.Skip) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (Inst asm.Skip) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  apply sim_alu with [ArithI (ADDI (n2w 0, n2w 0, n2w 0))]; [exact Hs|exact Hr|reflexivity|discriminate|reflexivity| |].
  - rewrite <- Hasm. reflexivity.
  - intros r H0 H1 H2 H3 H4 H5. rewrite <- Hasm. cbn [arun aexec aregs A0_of riscv_targetProof.A0_of]. regs_simp.
    apply Hg; assumption.
Qed.

Lemma imm_ok_range b (w : word64) : reg_imm_ok (inl b) (Imm w) riscv_config = true ->
  (if bool_decide (b = Sub) then (-2047 <= w2i w <= 2047)%Z else (-2048 <= w2i w <= 2047)%Z).
Proof.
  unfold reg_imm_ok, valid_imm; cbn [riscv_config]. rewrite Bool.orb_true_iff, !Bool.andb_true_iff, !bool_decide_spec.
  intros [[Hx Hm]|[Hlo Hhi]].
  - injection Hx as ->. subst w. cbn [bool_decide decide]. vm_compute. split; discriminate.
  - apply word_le_w2i in Hhi. rewrite w2i_max12 in Hhi.
    destruct (decide (b = Sub)) as [->|Hne].
    + rewrite (proj2 (bool_decide_spec (inl Sub = inl Sub)) eq_refl) in Hlo. apply word_lt_w2i in Hlo.
      rewrite w2i_min12 in Hlo. rewrite (proj2 (bool_decide_spec (Sub = Sub)) eq_refl). lia.
    + replace (bool_decide (inl b = inl Sub)) with false in Hlo
        by (symmetry; apply Bool.not_true_iff_false; rewrite bool_decide_spec; congruence).
      apply word_le_w2i in Hlo. rewrite w2i_min12 in Hlo.
      replace (bool_decide (b = Sub)) with false
        by (symmetry; apply Bool.not_true_iff_false; rewrite bool_decide_spec; congruence). lia.
Qed.

Ltac and_facts H :=
  repeat match type of H with
  | (_ && _)%bool = true => apply Bool.andb_true_iff in H; let H1 := fresh "Hok" in destruct H as [H1 H]; and_facts H1
  | reg_ok _ _ = true => apply reg_ok_iff in H
  end.

Lemma nbd_true (P : Prop) `{Decision P} : negb (bool_decide P) = true -> ~ P.
Proof. intros H1 H2. apply (proj2 (bool_decide_spec P)) in H2. rewrite H2 in H1. discriminate. Qed.

Ltac neq_facts :=
  repeat match goal with
  | H : negb (bool_decide _) = true |- _ => apply nbd_true in H
  | H : true = true |- _ => clear H
  end.

Ltac isa_simp H :=
  repeat match type of H with
  | context [bool_decide (ISA riscv_config = ?y)] =>
      let v := eval vm_compute in (bool_decide (ISA riscv_config = y)) in
      change (bool_decide (ISA riscv_config = y)) with v in H
  | context [list.MEM (ISA riscv_config) ?l] =>
      let v := eval vm_compute in (list.MEM (ISA riscv_config) l) in
      change (list.MEM (ISA riscv_config) l) with v in H
  | context [ISA riscv_config] => change (ISA riscv_config) with RISC_V in H
  end; cbn [implb orb andb] in H.

Lemma dec_eqb {A} (a b : N) (x y : A) : (if decide (a = b) then x else y) = (if a =? b then x else y).
Proof. destruct (decide (a = b)), (N.eqb_spec a b); congruence. Qed.

Ltac fin_regs Hg :=
  unfold UPDATE; rewrite ?dec_eqb; eqb_simp;
  repeat (match goal with
  | |- context [N.eqb ?a ?b] => destruct (N.eqb_spec a b); [first [subst a | subst b | idtac]|]
  end; eqb_simp); try lia; rewrite ?Hg by lia;
  try (lazymatch goal with
       | |- ?x = ?x => reflexivity
       | |- context [aload] => fail
       | |- context [astore] => fail
       | _ => reflexivity end).

Lemma sim_binop_reg s1 s2 ms b r1 r2 r3 :
  asm_step riscv_config s1 (Inst (Arith (Binop b r1 r2 (Reg r3)))) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (Inst (Arith (Binop b r1 r2 (Reg r3)))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok reg_imm_ok two_reg_arith riscv_config implb] in Hok. and_facts Hok.
  apply sim_alu with [ArithR (riscv_bop_r b (n2w r1, n2w r2, n2w r3))]; [exact Hs|exact Hr|destruct b; reflexivity|discriminate| | |].
  - destruct b; reflexivity.
  - rewrite <- Hasm. destruct b; reflexivity.
  - intros r H0 H1 H2 H3 H4 H5. rewrite <- Hasm.
    destruct b; cbn [arun aexec aregs A0_of riscv_targetProof.A0_of riscv_bop_r asmSem.asm inst arith_upd binop_upd upd_reg upd_pc set_regs
      set_pc regs read_reg reg_imm]; regs_simp; fin_regs Hg.
Qed.

Lemma sim_binop_imm s1 s2 ms b r1 r2 w :
  asm_step riscv_config s1 (Inst (Arith (Binop b r1 r2 (Imm w)))) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (Inst (Arith (Binop b r1 r2 (Imm w)))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok two_reg_arith riscv_config implb] in Hok.
  apply Bool.andb_true_iff in Hok as [Hok Himm]. and_facts Hok. apply imm_ok_range in Himm.
  destruct b; match type of Himm with context [bool_decide ?P] =>
    let v := eval vm_compute in (bool_decide P) in change (bool_decide P) with v in Himm end; cbv iota in Himm.
  1,3,4,5: match goal with |- enc_goal _ (Inst (Arith (Binop ?b _ _ _))) _ _ =>
    apply sim_alu with [ArithI (riscv_bop_i b (n2w r1, n2w r2, w2w w))] end;
    [exact Hs|exact Hr|reflexivity|discriminate|reflexivity|rewrite <- Hasm; reflexivity|];
    intros r H0 H1 H2 H3 H4 H5; rewrite <- Hasm;
    cbn [arun aexec aregs A0_of riscv_targetProof.A0_of riscv_bop_i asmSem.asm inst arith_upd binop_upd upd_reg upd_pc set_regs
      set_pc regs read_reg reg_imm]; regs_simp; rewrite imm12_id by exact Himm; fin_regs Hg.
  apply sim_alu with [ArithI (ADDI (n2w r1, n2w r2, word_2comp (w2w w)))];
    [exact Hs|exact Hr|reflexivity|discriminate|reflexivity|rewrite <- Hasm; reflexivity|].
  intros r H0 H1 H2 H3 H4 H5; rewrite <- Hasm.
  cbn [arun aexec aregs A0_of riscv_targetProof.A0_of asmSem.asm inst arith_upd binop_upd upd_reg upd_pc set_regs
    set_pc regs read_reg reg_imm]; regs_simp. rewrite imm12_neg by exact Himm. fin_regs Hg.
Qed.

Lemma w2n_n2w6 n : n < 64 -> w2n (n2w n : word6) = n.
Proof. intros H. rewrite w2n_n2w. apply N.mod_small. exact H. Qed.

Lemma w2n_ext6 (y : word64) : w2n (w2w (word_extract 5 0 y : word6) : word64) = w2n y mod 64.
Proof.
  unfold w2w at 1. rewrite w2n_n2w. change (dimword 64) with (2 ^ 64).
  unfold word_extract, w2w, word_bits. rewrite !w2n_n2w. change (dimword 6) with 64. change (dimword 64) with (2 ^ 64).
  rewrite MIN_min. change (N.min 5 (dimindex 64 - 1)) with 5. rewrite BITS_0_mod. change (2 ^ N.succ 5) with 64.
  pose proof (N.mod_lt (w2n y) 64 ltac:(discriminate)).
  rewrite !(N.mod_small (w2n y mod 64)) by lia. reflexivity.
Qed.

Ltac asm_unfold :=
  cbn [arun aexec aregs A0_of riscv_targetProof.A0_of riscv_bop_i riscv_sh riscv_shv asmSem.asm inst arith_upd binop_upd upd_reg upd_pc
       set_regs set_pc regs read_reg reg_imm word_shift assert set_failed];
  try unfold temp_reg; try unfold read_reg.

Lemma sim_shift_imm s1 s2 ms sh r1 r2 w :
  asm_step riscv_config s1 (Inst (Arith (asm.Shift sh r1 r2 (Imm w)))) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (Inst (Arith (asm.Shift sh r1 r2 (Imm w)))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok two_reg_arith riscv_config implb] in Hok.
  apply Bool.andb_true_iff in Hok as [Hok Himm]. apply Bool.andb_true_iff in Himm as [Hz Hw].
  apply N.ltb_lt in Hw. change (dimindex 64) with 64 in Hw. and_facts Hok.
  destruct sh.
  1-3: match goal with |- enc_goal _ (Inst (Arith (asm.Shift ?sh _ _ _))) _ _ =>
    apply sim_alu with [Shift (riscv_sh sh (n2w r1, n2w r2, n2w (w2n w)))] end;
    [exact Hs|exact Hr|reflexivity|discriminate|reflexivity|rewrite <- Hasm; reflexivity|];
    intros r H0 H1 H2 H3 H4 H5; rewrite <- Hasm; asm_unfold; regs_simp; rewrite w2n_n2w6 by exact Hw; fin_regs Hg.
  assert (Hw0 : w2n w <> 0).
  { intros E. apply lemmas.w2n_eq_0 in E. subst w. cbn in Hz. discriminate Hz. }
  apply sim_alu with [Shift (SRLI (temp_reg, n2w r2, n2w (w2n w)));
                      Shift (SLLI (n2w r1, n2w r2, n2w (64 - w2n w)));
                      ArithR (OR (n2w r1, n2w r1, temp_reg))];
    [exact Hs|exact Hr|reflexivity|discriminate|reflexivity|rewrite <- Hasm; reflexivity|].
  intros r H0 H1 H2 H3 H4 H5; rewrite <- Hasm; asm_unfold; regs_simp.
  rewrite !w2n_n2w6 by lia. fin_regs Hg.
  apply ror_thm. lia.
Qed.

Lemma ror_reg (x y : word64) : w2n y < 64 ->
  word_or (word_lsr x (w2n y mod 64))
    (word_lsl x (w2n (word_sub (word_or (n2w 0) (sw2sw (n2w 64 : word12))) y) mod 64)) = word_ror x (w2n y).
Proof.
  intros Hy. change (word_or (n2w 0) (sw2sw (n2w 64 : word12)) : word64) with (n2w 64 : word64).
  rewrite lemmas.word_sub_w2n by (apply lemmas.WORD_LS; rewrite w2n_n2w; cbn; lia).
  rewrite w2n_n2w. change (64 mod dimword 64) with 64. rewrite (N.mod_small (w2n y)) by exact Hy.
  destruct (N.eq_dec (w2n y) 0) as [E|E].
  - rewrite E. change ((64 - 0) mod 64) with 0. apply word_bit_ext; intros i Hi.
    rewrite word_ror_def, fcp_index_FCP by exact Hi. rewrite wb_fcp by exact Hi.
    rewrite wb_or, wb_lsl, wb_lsr. change (dimindex 64) with 64 in *.
    rewrite N.add_0_r, N.sub_0_r, N.mod_small by exact Hi. rewrite wb_fcp by exact Hi.
    destruct (N.ltb_spec i 64); [|lia]. destruct (N.leb_spec 0 i); [|lia]. cbn [andb].
    rewrite ?N.sub_0_r. destruct (word_bit i x); reflexivity.
  - rewrite N.mod_small by lia. rewrite lemmas.WORD_OR_COMM. apply ror_thm. exact Hy.
Qed.

Lemma sim_shift_reg s1 s2 ms sh r1 r2 r3 :
  asm_step riscv_config s1 (Inst (Arith (asm.Shift sh r1 r2 (Reg r3)))) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (Inst (Arith (asm.Shift sh r1 r2 (Reg r3)))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok two_reg_arith riscv_config implb] in Hok. and_facts Hok.
  assert (Hlt : w2n (s1.(regs) r3) < 64).
  { rewrite <- Hasm in Hf. cbn [asmSem.asm inst arith_upd assert set_failed upd_pc set_pc failed read_reg] in Hf.
    apply Bool.orb_false_iff in Hf as [Hf _]. apply Bool.negb_false_iff, N.ltb_lt in Hf. exact Hf. }
  destruct sh.
  1-3: match goal with |- enc_goal _ (Inst (Arith (asm.Shift ?sh _ _ _))) _ _ =>
    apply sim_alu with [Shift (riscv_shv sh (n2w r1, n2w r2, n2w r3))] end;
    [exact Hs|exact Hr|reflexivity|discriminate|reflexivity|rewrite <- Hasm; reflexivity|];
    intros r H0 H1 H2 H3 H4 H5; rewrite <- Hasm; asm_unfold; regs_simp;
    unfold word_lsl_bv, word_lsr_bv, word_asr_bv; rewrite ?w2n_ext6; fin_regs Hg;
    rewrite N.mod_small by exact Hlt; reflexivity.
  apply sim_alu with [ArithI (ORI (temp_reg, n2w 0, n2w 64)); ArithR (SUB (temp_reg, temp_reg, n2w r3));
         Shift (SLL (temp_reg, n2w r2, temp_reg)); Shift (SRL (n2w r1, n2w r2, n2w r3));
         ArithR (OR (n2w r1, n2w r1, temp_reg))];
    [exact Hs|exact Hr|reflexivity|discriminate|reflexivity|rewrite <- Hasm; reflexivity|].
  intros r H0 H1 H2 H3 H4 H5; rewrite <- Hasm; asm_unfold; regs_simp.
  unfold word_lsl_bv, word_lsr_bv, word_asr_bv; rewrite ?w2n_ext6. fin_regs Hg.
  apply ror_reg, Hlt.
Qed.

Lemma sim_div s1 s2 ms r1 r2 r3 :
  asm_step riscv_config s1 (Inst (Arith (Div r1 r2 r3))) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (Inst (Arith (Div r1 r2 r3))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok riscv_config] in Hok. and_facts Hok.
  assert (Hq : bool_decide (s1.(regs) r3 = n2w 0) = false).
  { rewrite <- Hasm in Hf. cbn [asmSem.asm inst arith_upd assert set_failed upd_pc set_pc failed read_reg] in Hf.
    apply Bool.orb_false_iff in Hf as [Hf _]. apply Bool.negb_false_iff, Bool.negb_true_iff in Hf. exact Hf. }
  apply sim_alu with [MulDiv (riscv.DIV (n2w r1, n2w r2, n2w r3))];
    [exact Hs|exact Hr|reflexivity|discriminate|reflexivity|rewrite <- Hasm; reflexivity|].
  intros r H0 H1 H2 H3 H4 H5; rewrite <- Hasm; asm_unfold; regs_simp. rewrite !(Hg r3) by lia. rewrite Hq.
  fin_regs Hg.
Qed.

Lemma sim_longmul s1 s2 ms r1 r2 r3 r4 :
  asm_step riscv_config s1 (Inst (Arith (LongMul r1 r2 r3 r4))) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (Inst (Arith (LongMul r1 r2 r3 r4))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok riscv_config] in Hok. isa_simp Hok. and_facts Hok. neq_facts.
  apply sim_alu with [MulDiv (MULHU (n2w r1, n2w r3, n2w r4)); MulDiv (MUL (n2w r2, n2w r3, n2w r4))];
    [exact Hs|exact Hr|reflexivity|discriminate|reflexivity|rewrite <- Hasm; reflexivity|].
  intros r H0 H1 H2 H3 H4 H5; rewrite <- Hasm; asm_unfold; regs_simp. fin_regs Hg.
  all: first [ rewrite <- mul_long_thm; change (dimword 64) with 18446744073709551616; reflexivity
             | unfold word_mul; reflexivity ].
Qed.

Lemma sim_addcarry s1 s2 ms r1 r2 r3 r4 :
  asm_step riscv_config s1 (Inst (Arith (AddCarry r1 r2 r3 r4))) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (Inst (Arith (AddCarry r1 r2 r3 r4))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok riscv_config two_reg_arith] in Hok. isa_simp Hok. and_facts Hok. neq_facts.
  apply sim_alu with (riscv_ast (Inst (Arith (AddCarry r1 r2 r3 r4))));
    [exact Hs|exact Hr|reflexivity|discriminate|reflexivity|rewrite <- Hasm; reflexivity|].
  intros r H0 H1 H2 H3 H4 H5; rewrite <- Hasm; cbn [riscv_ast]; asm_unfold; regs_simp. fin_regs Hg.
  - apply addcarry_flag.
  - apply addcarry_sum.
Qed.

Lemma sim_addoverflow s1 s2 ms r1 r2 r3 r4 :
  asm_step riscv_config s1 (Inst (Arith (AddOverflow r1 r2 r3 r4))) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (Inst (Arith (AddOverflow r1 r2 r3 r4))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok riscv_config two_reg_arith] in Hok. isa_simp Hok. and_facts Hok. neq_facts.
  apply sim_alu with (riscv_ast (Inst (Arith (AddOverflow r1 r2 r3 r4))));
    [exact Hs|exact Hr|reflexivity|discriminate|reflexivity|rewrite <- Hasm; reflexivity|].
  intros r H0 H1 H2 H3 H4 H5; rewrite <- Hasm; cbn [riscv_ast]; asm_unfold; regs_simp. fin_regs Hg.
  apply addovf_val.
Qed.

Lemma sim_suboverflow s1 s2 ms r1 r2 r3 r4 :
  asm_step riscv_config s1 (Inst (Arith (SubOverflow r1 r2 r3 r4))) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (Inst (Arith (SubOverflow r1 r2 r3 r4))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok riscv_config two_reg_arith] in Hok. isa_simp Hok. and_facts Hok. neq_facts.
  apply sim_alu with (riscv_ast (Inst (Arith (SubOverflow r1 r2 r3 r4))));
    [exact Hs|exact Hr|reflexivity|discriminate|reflexivity|rewrite <- Hasm; reflexivity|].
  intros r H0 H1 H2 H3 H4 H5; rewrite <- Hasm; cbn [riscv_ast]; asm_unfold; regs_simp. fin_regs Hg.
  apply subovf_val.
Qed.

(** ** Constants and memory instructions (Galette-only) *)

Ltac fcp_to_wb H :=
  repeat match type of H with context [@fcp_index ?a ?w ?k] =>
    rewrite (@wb_fcp a w k) in H by reflexivity end.

Ltac const_list E :=
  eassert (Hl : riscv_ast (Inst (Const _ _)) = _)
    by (cbn [riscv_ast]; rewrite ?E; cbn [andb orb negb]; cbv iota;
        unfold riscv_const32; rewrite ?E; cbv iota; cbn [app]; reflexivity).

Lemma sim_const s1 s2 ms r i :
  asm_step riscv_config s1 (Inst (Const r i)) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (Inst (Const r i)) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok] in Hok. apply reg_ok_iff in Hok.
  destruct (bool_decide (i = sw2sw (word_extract 11 0 i : word12))) eqn:E1.
  { eassert (Hl : riscv_ast (Inst (Const r i)) = _) by (cbn [riscv_ast]; rewrite E1; reflexivity).
    apply sim_alu with (1 := Hs) (2 := Hr) (3 := Hl); [discriminate|reflexivity|rewrite <- Hasm; reflexivity|].
    intros r' H0 H1 H2 H3 H4 H5; rewrite <- Hasm; asm_unfold; regs_simp.
    apply bool_decide_spec in E1. rewrite (proj1 (proj2 (proj2 (lemmas.WORD_OR_CLAUSES _)))), <- E1. fin_regs Hg. }
  destruct (fcp_index i 31) eqn:E4;
    [destruct (bool_decide ((word_extract 63 32 i : word32) = word_2comp (n2w 1))) eqn:Em
    |destruct (bool_decide ((word_extract 63 32 i : word32) = n2w 0)) eqn:Ez];
    destruct (fcp_index (word_extract 31 0 i : word32) 11) eqn:E3;
    try match goal with
        | H : bool_decide (_ = word_2comp (n2w 1)) = false |- _ =>
            destruct (fcp_index (word_1comp (word_extract 63 32 i : word32)) 11) eqn:E5
        | H : bool_decide (_ = n2w 0) = false |- _ =>
            destruct (fcp_index (word_extract 63 32 i : word32) 11) eqn:E6
        end.
  all: eassert (Hl : riscv_ast (Inst (Const r i)) = _)
    by (cbn [riscv_ast]; rewrite E1; cbv iota; rewrite E4; rewrite ?Ez, ?Em;
        rewrite ?Bool.andb_false_r; cbn [andb orb negb]; cbv iota;
        unfold riscv_const32; rewrite ?E3, ?E5, ?E6; cbv iota; cbn [app]; reflexivity).
  all: apply sim_alu with (1 := Hs) (2 := Hr) (3 := Hl); [discriminate|reflexivity|rewrite <- Hasm; reflexivity|].
  all: intros r' H0 H1 H2 H3 H4 H5; rewrite <- Hasm; asm_unfold; regs_simp; fin_regs Hg.
  all: try fcp_to_wb E3; try fcp_to_wb E4; try fcp_to_wb E5; try fcp_to_wb E6.
  all: repeat match goal with
         | |- context [word_xor (sw2sw (word_concat (word_1comp (word_extract 31 12 ?w)) (n2w 0)))
                                (sw2sw (word_extract 11 0 ?w))] => rewrite (const32_xori w) by assumption
         | |- context [word_add (sw2sw (word_concat (word_extract 31 12 ?w) (n2w 0)))
                                (sw2sw (word_extract 11 0 ?w))] => rewrite (const32_addi w) by assumption
         end.
  all: try change (w2n (n2w 32 : word6)) with 32.
  all: lazymatch goal with
       | |- word_or _ _ = _ => apply combine64_or; assumption
       | |- word_xor _ _ = _ => apply combine64_xor; assumption
       | |- sw2sw _ = _ => apply (const32_cond i); rewrite <- (wb_fcp i 31) in E4 by reflexivity; rewrite E4;
               rewrite ?Ez, ?Em; rewrite ?Bool.andb_false_r; reflexivity
       end.
Qed.

(** ** Memory instructions *)

Lemma rmw_facts n : forall (ad : word64) s, s.(be) = false ->
  fst (read_mem_word ad n s) = aload n s.(mem) ad /\
  (snd (read_mem_word ad n s)).(regs) = s.(regs) /\ (snd (read_mem_word ad n s)).(mem) = s.(mem) /\
  (snd (read_mem_word ad n s)).(mem_domain) = s.(mem_domain) /\
  ((snd (read_mem_word ad n s)).(failed) = false ->
   s.(failed) = false /\ forall k, k < n -> s.(mem_domain) (word_add ad (n2w k))).
Proof.
  induction n as [|n IH] using N.peano_ind; intros ad s Hbe.
  - cbn. split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]].
    intros Hf0; split; [exact Hf0|intros; lia].
  - rewrite (proj2 (read_mem_word_def ad n s)). rewrite Hbe.
    destruct (IH (word_add ad (n2w 1)) s Hbe) as (H1 & H2 & H3 & H4 & H5).
    destruct (read_mem_word (word_add ad (n2w 1)) n s) as [w s1] eqn:E. cbn [fst snd] in *.
    cbn [assert set_failed regs mem mem_domain failed]. unfold read_mem. rewrite aload_SUC, H1, H3.
    split; [reflexivity|split; [exact H2|split; [reflexivity|split; [exact H4|]]]].
    intros Hf. apply Bool.orb_false_iff in Hf as [Hd Hf]. apply H5 in Hf as [Hf Hk].
    split; [exact Hf|]. intros k Hk'.
    destruct (N.eq_dec k 0) as [->|Hk0].
    + rewrite add_n2w_0. destruct (classical_dec _) as [Hin|]; [rewrite <- H4; exact Hin|discriminate Hd].
    + replace k with (1 + (k - 1)) by lia. rewrite <- add_n2w_add. apply Hk. lia.
Qed.

Lemma wmw_facts n : forall (ad : word64) w s, s.(be) = false ->
  (write_mem_word ad n w s).(mem) = astore n ad w s.(mem) /\
  (write_mem_word ad n w s).(regs) = s.(regs) /\ (write_mem_word ad n w s).(mem_domain) = s.(mem_domain) /\
  ((write_mem_word ad n w s).(failed) = false ->
   s.(failed) = false /\ forall k, k < n -> s.(mem_domain) (word_add ad (n2w k))).
Proof.
  induction n as [|n IH] using N.peano_ind; intros ad w s Hbe.
  - cbn. split; [reflexivity|split; [reflexivity|split; [reflexivity|]]].
    intros Hf0; split; [exact Hf0|intros; lia].
  - rewrite (proj2 (write_mem_word_def ad n w s)). rewrite Hbe. cbv zeta.
    destruct (IH (word_add ad (n2w 1)) (word_lsr w 8) s Hbe) as (H1 & H2 & H3 & H4).
    cbn [assert set_failed upd_mem set_mem regs mem mem_domain failed].
    rewrite H1, astore_SUC. split; [reflexivity|split; [exact H2|split; [exact H3|]]].
    intros Hf. apply Bool.orb_false_iff in Hf as [Hd Hf]. apply H4 in Hf as [Hf Hk].
    split; [exact Hf|]. intros k Hk'.
    destruct (N.eq_dec k 0) as [->|Hk0].
    + rewrite add_n2w_0. destruct (classical_dec _) as [Hin|]; [rewrite <- H3; exact Hin|discriminate Hd].
    + replace k with (1 + (k - 1)) by lia. rewrite <- add_n2w_add. apply Hk. lia.
Qed.

Lemma load_facts n r1 r2 w pc' s1 s2 :
  s1.(be) = false -> upd_pc pc' (mem_load n r1 (Addr r2 w) s1) = s2 -> s2.(failed) = false ->
  s2.(pc) = pc' /\ s2.(mem) = s1.(mem) /\
  s2.(regs) = UPDATE r1 (aload n s1.(mem) (word_add (s1.(regs) r2) w)) s1.(regs) /\
  aligned (LOG2 n) (word_add (s1.(regs) r2) w) = true /\
  (forall k, k < n -> s1.(mem_domain) (word_add (word_add (s1.(regs) r2) w) (n2w k))).
Proof.
  intros Hbe <- Hf. unfold mem_load, addr, read_reg in *. cbv zeta in *. rewrite Hbe in *.
  pose proof (rmw_facts n (word_add (regs s1 r2) w) s1 Hbe) as (R1 & R2 & R3 & R4 & R5).
  destruct (read_mem_word (word_add (regs s1 r2) w) n s1) as [v s'] eqn:E. cbn [fst snd] in *.
  cbn [upd_pc set_pc assert set_failed upd_reg set_regs failed regs mem pc mem_domain] in Hf |- *.
  apply Bool.orb_false_iff in Hf as [Hal Hf]. apply Bool.negb_false_iff in Hal.
  apply R5 in Hf as [_ Hdom]. subst v. rewrite R2, R3.
  split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [exact Hal|exact Hdom]]]].
Qed.

Lemma store_facts n r1 r2 w pc' s1 s2 :
  s1.(be) = false -> upd_pc pc' (mem_store n r1 (Addr r2 w) s1) = s2 -> s2.(failed) = false ->
  s2.(pc) = pc' /\ s2.(mem) = astore n (word_add (s1.(regs) r2) w) (s1.(regs) r1) s1.(mem) /\
  s2.(regs) = s1.(regs) /\
  aligned (LOG2 n) (word_add (s1.(regs) r2) w) = true /\
  (forall k, k < n -> s1.(mem_domain) (word_add (word_add (s1.(regs) r2) w) (n2w k))).
Proof.
  intros Hbe <- Hf. unfold mem_store, addr, read_reg in *. cbv zeta in *. rewrite Hbe in *.
  pose proof (wmw_facts n (word_add (regs s1 r2) w) (regs s1 r1) s1 Hbe) as (W1 & W2 & W3 & W4).
  cbn [upd_pc set_pc assert set_failed failed regs mem pc mem_domain] in Hf |- *.
  apply Bool.orb_false_iff in Hf as [Hal Hf]. apply Bool.negb_false_iff in Hal.
  apply W4 in Hf as [_ Hdom].
  split; [reflexivity|split; [exact W1|split; [exact W2|split; [exact Hal|exact Hdom]]]].
Qed.

Lemma asm_Load r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (Mem asm.Load r1 a)) pc' s = upd_pc pc' (mem_load 8 r1 a s).
Proof. reflexivity. Qed.
Lemma asm_Load8 r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (Mem Load8 r1 a)) pc' s = upd_pc pc' (mem_load 1 r1 a s).
Proof. reflexivity. Qed.
Lemma asm_Load16 r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (Mem Load16 r1 a)) pc' s = upd_pc pc' (mem_load 2 r1 a s).
Proof. reflexivity. Qed.
Lemma asm_Load32 r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (Mem Load32 r1 a)) pc' s = upd_pc pc' (mem_load 4 r1 a s).
Proof. reflexivity. Qed.
Lemma asm_Store r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (Mem asm.Store r1 a)) pc' s = upd_pc pc' (mem_store 8 r1 a s).
Proof. reflexivity. Qed.
Lemma asm_Store8 r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (Mem Store8 r1 a)) pc' s = upd_pc pc' (mem_store 1 r1 a s).
Proof. reflexivity. Qed.
Lemma asm_Store16 r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (Mem Store16 r1 a)) pc' s = upd_pc pc' (mem_store 2 r1 a s).
Proof. reflexivity. Qed.
Lemma asm_Store32 r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (Mem Store32 r1 a)) pc' s = upd_pc pc' (mem_store 4 r1 a s).
Proof. reflexivity. Qed.

Lemma offset12 (w : word64) : offset_ok 0 (min12, max12) w = true -> (-2048 <= w2i w <= 2047)%Z.
Proof.
  unfold offset_ok. rewrite !Bool.andb_true_iff. intros ((H1 & H2) & _).
  apply word_le_w2i in H1, H2. rewrite w2i_min12 in H1. rewrite w2i_max12 in H2. lia.
Qed.

Lemma sim_mem s1 s2 ms m r1 r2 w :
  asm_step riscv_config s1 (Inst (Mem m r1 (Addr r2 w))) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (Inst (Mem m r1 (Addr r2 w))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  pose proof Hs as (Hb & _).
  cbn [asm_ok inst_ok] in Hok. apply Bool.andb_true_iff in Hok as [Hok Hoff]. and_facts Hok.
  assert (Hw : (-2048 <= w2i w <= 2047)%Z).
  { destruct m;
      repeat match type of Hoff with context [list.MEM ?x ?l] =>
        let v := eval vm_compute in (list.MEM x l) in change (list.MEM x l) with v in Hoff end;
      cbv iota in Hoff; isa_simp Hoff;
      unfold addr_offset_ok, hw_offset_ok, byte_offset_ok in Hoff; cbn [riscv_config addr_offset hw_offset byte_offset] in Hoff;
      rewrite ?Bool.andb_true_iff in Hoff; try (match type of Hoff with _ /\ _ => destruct Hoff as [Hoff _] end); apply offset12, Hoff. }
  set (ad := word_add (s1.(regs) r2) w).
  assert (Had : word_add (rreg (aregs (A0_of s1 ms)) (n2w r2)) (sw2sw (w2w w : word12)) = ad).
  { cbn [aregs A0_of riscv_targetProof.A0_of]. regs_simp. rewrite Hg by lia. rewrite imm12_id by exact Hw. reflexivity. }
  assert (Hpc4 : word_add s1.(pc) (n2w (LENGTH (riscv_enc (Inst (Mem m r1 (Addr r2 w)))))) = word_add s1.(pc) (n2w 4))
    by (destruct m; reflexivity).
  assert (Hb1 : bytes_in_memory s1.(pc) (riscv_encode (hd (ArithI (ADDI (n2w 0, n2w 0, n2w 0))) (riscv_ast (Inst (Mem m r1 (Addr r2 w))))))
                  s1.(mem) s1.(mem_domain)).
  { rewrite riscv_enc_flat in Hb. destruct m; cbn [riscv_ast riscv_memop MAP FLAT List.map List.concat hd] in Hb |- *;
      rewrite app_nil_r in Hb; exact Hb. }
  assert (Hal4 : aligned 2 (word_add s1.(pc) (n2w (4 * 1))) = true) by (apply aligned_add4, Hal).
  pose proof Hasm as Hasm'. rewrite Hpc4 in Hasm'.
  destruct m; cbn [riscv_ast riscv_memop hd] in Hb1;
    first [ rewrite asm_Load in Hasm' | rewrite asm_Load8 in Hasm' | rewrite asm_Load16 in Hasm'
          | rewrite asm_Load32 in Hasm' | rewrite asm_Store in Hasm' | rewrite asm_Store8 in Hasm'
          | rewrite asm_Store16 in Hasm' | rewrite asm_Store32 in Hasm' ];
    first [ destruct (load_facts _ _ _ _ _ _ _ Hbe Hasm' Hf) as (F1 & F2 & F3 & F4 & F5)
          | destruct (store_facts _ _ _ _ _ _ _ Hbe Hasm' Hf) as (F1 & F2 & F3 & F4 & F5) ];
    fold ad in F2, F3, F4, F5;
    change (LOG2 8) with 3 in F4; change (LOG2 4) with 2 in F4; change (LOG2 2) with 1 in F4;
    change (LOG2 1) with 0 in F4.
  all: unfold A0_of in *.
  all: match goal with |- enc_goal _ (Inst (Mem ?mm _ _)) _ _ =>
    eapply (enc_sim s1 _ _ ms (riscv_ast (Inst (Mem mm r1 (Addr r2 w)))) Hs Hr); [discriminate| |] end.
  all: assert (Had' : word_add (rreg (riscv_targetProof.gregs (embedriscv_state ms)) (n2w r2)) (sw2sw (w2w w : word12)) = ad) by exact Had.
  all: assert (Had'' : word_add (riscv_targetProof.gregs (embedriscv_state ms) (n2w r2)) (sw2sw (w2w w : word12)) = ad)
         by (rewrite Hg by lia; rewrite imm12_id by exact Hw; reflexivity).
  all: cbn [riscv_ast riscv_memop run_ok arun].
  all: try (split; [reflexivity|split; [exact Hb1|split; [cbn [mem_ok aregs A0_of riscv_targetProof.A0_of]; rewrite ?Had'; first [exact F4|exact Logic.I]
           |split; [cbn [acc_ok aregs A0_of riscv_targetProof.A0_of]; rewrite ?Had'; exact F5|cbn [aexec apc A0_of riscv_targetProof.A0_of]; exact Hal4]]]]).
  all: unfold QA_of; cbn [aexec aregs apc amem A0_of riscv_targetProof.A0_of]; rewrite ?Had'.
  all: split; [rewrite F1; reflexivity|split].
  all: try (intros a Ha; rewrite F2; regs_simp; rewrite ?Had', ?Had'', ?(Hg r1) by lia;
            lazymatch goal with |- ?x = ?x => reflexivity end).
  all: intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3 & H4 & H5); rewrite F3; regs_simp; rewrite ?Had', ?Had''; fin_regs Hg.
Qed.

(** ** Jumps, calls and Loc (Galette-only) *)

(** ** Jumps and [Loc] *)

Lemma len_enc i : LENGTH (riscv_encode i) = 4.
Proof. reflexivity. Qed.

Ltac split_bytes H :=
  rewrite riscv_enc_flat in H;
  cbn [riscv_ast MAP FLAT List.map List.concat] in H;
  rewrite ?app_nil_r in H;
  repeat match type of H with
  | bytes_in_memory _ (riscv_encode _ ++ _) _ _ =>
      let H1 := fresh "Hb" in apply bytes_in_memory_APPEND in H as [H1 H]; rewrite len_enc in H
  end.

Lemma word_bit0_aligned (x : word64) k : aligned k x = true -> 0 < k -> word_bit 0 x = false.
Proof. intros H Hk. apply (aligned_wb k); assumption. Qed.

Lemma aligned_add (x y : word64) k : aligned k x = true -> aligned k y = true -> aligned k (word_add x y) = true.
Proof. intros Hx Hy. rewrite (proj1 (alignment.aligned_add_sub k x y Hy)). exact Hx. Qed.

Lemma aligned_2_1 (x : word64) : aligned 2 x = true -> aligned 1 x = true.
Proof. intros H. apply (alignment.aligned_imp 1 2 x). split; [lia|exact H]. Qed.

Lemma jump_off_ok (w : word64) : jump_offset_ok riscv_config w = true ->
  (-2147483648 <= w2i w <= 2147481599)%Z /\ aligned 2 w = true.
Proof.
  unfold jump_offset_ok, offset_ok; cbn [riscv_config jump_offset code_alignment].
  rewrite !Bool.andb_true_iff. intros ((H1 & H2) & H3). apply word_le_w2i in H1, H2.
  rewrite w2i_min32 in H1. change (w2i (n2w 2147481599 : word64)) with 2147481599%Z in H2. auto.
Qed.

Lemma sim_alu_gen s1 i s2 ms l :
  asm_step riscv_config s1 i s2 -> target_state_rel riscv_target s1 ms ->
  riscv_ast i = l -> l <> [] -> forallb is_alu l = true ->
  s2.(pc) = word_add s1.(pc) (n2w (LENGTH (riscv_enc i))) -> s2.(mem) = s1.(mem) ->
  (forall r, r < 32 -> r <> 0 -> r <> 2 -> r <> 3 -> r <> 4 -> r <> 31 ->
     aregs (arun (A0_of s1 ms) l) (n2w r) = s2.(regs) r) ->
  enc_goal s1 i s2 ms.
Proof.
  intros Hs Hr Hl Hne Hall Hpc2 Hm Hregs.
  destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & _ & Hasm & _).
  pose proof Hs as (Hb & _).
  destruct (alu_run s1 i s1.(mem_domain) l (A0_of s1 ms) Hal Hl Hne Hall Hb eq_refl eq_refl)
    as (Hrun & Hpc & Hmem).
  unfold A0_of in *.
  apply (enc_sim s1 i s2 ms l Hs Hr Hne Hrun).
  split; [|split].
  - rewrite Hpc, Hpc2. reflexivity.
  - intros a Ha. rewrite Hmem, Hm. reflexivity.
  - intros r Hr0 Hav. apply avoid_iff in Hav as (H0 & H2 & H3 & H4 & H31). apply Hregs; assumption.
Qed.

Lemma loc_ok_range (w : word64) : loc_offset_ok riscv_config w = true ->
  (-2147483648 <= w2i w <= 2147481599)%Z /\ aligned 2 w = true.
Proof. exact (jump_off_ok w). Qed.

Lemma sim_loc s1 s2 ms r w :
  asm_step riscv_config s1 (Loc r w) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (Loc r w) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok] in Hok. apply Bool.andb_true_iff in Hok as [Hok Hw]. apply reg_ok_iff in Hok.
  apply loc_ok_range in Hw as [Hw _].
  apply sim_alu_gen with (riscv_ast (Loc r w)); [exact Hs|exact Hr|reflexivity|discriminate|reflexivity
    |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
  intros r' H0 H1 H2 H3 H4 H5; rewrite <- Hasm; cbn [riscv_ast]; asm_unfold; regs_simp; fin_regs Hg.
  rewrite <- lemmas.WORD_ADD_ASSOC. rewrite hi_lo by exact Hw. reflexivity.
Qed.

Lemma near21 (a : word64) : (word_le min21 a && word_le a max21)%bool = true -> aligned 2 a = true ->
  word_lsl (sw2sw (w2w (word_lsr a 1) : word20) : word64) 1 = a.
Proof.
  intros H Ha. apply Bool.andb_true_iff in H as [H1 H2]. apply word_le_w2i in H1, H2.
  rewrite w2i_min21 in H1. rewrite w2i_max21 in H2.
  apply branch_off0; [vm_compute; discriminate|apply aligned_2_1, Ha|].
  change (INT_MIN 20) with (-524288)%Z. change (INT_MAX 20) with 524287%Z.
  pose proof (Z.div_mod (w2i a) 2 ltac:(lia)); pose proof (Z.mod_pos_bound (w2i a) 2 ltac:(lia)); lia.
Qed.

Lemma bytes1 i l (pc : word64) m d : bytes_in_memory pc (FLAT (MAP riscv_encode (i :: l))) m d ->
  bytes_in_memory pc (riscv_encode i) m d /\ bytes_in_memory (word_add pc (n2w 4)) (FLAT (MAP riscv_encode l)) m d.
Proof. cbn [MAP FLAT List.map List.concat]. rewrite bytes_in_memory_APPEND, len_enc. auto. Qed.

Lemma pcs_in i (pc : word64) k : 4 * k < LENGTH (riscv_enc i) ->
  word_add pc (n2w (4 * k)) IN all_pcs (LENGTH (riscv_enc i)) pc 2.
Proof. intros H. exists k. change (2 ** 2) with 4. split; [f_equal; f_equal; lia|lia]. Qed.

Lemma sim_jump s1 s2 ms a :
  asm_step riscv_config s1 (Jump a) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (Jump a) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  pose proof Hs as (Hb & _). cbn [asm_ok] in Hok. apply jump_off_ok in Hok as [Hw Ha].
  rewrite riscv_enc_flat in Hb.
  destruct (word_le min21 a && word_le a max21)%bool eqn:Er.
  - assert (Hl : riscv_ast (Jump a) = [Branch (JAL (n2w 0, w2w (word_lsr a 1)))]) by (cbn [riscv_ast]; rewrite Er; reflexivity).
    rewrite Hl in Hb. apply bytes1 in Hb as [Hb0 _].
    unfold A0_of in *.
  apply (enc_sim s1 _ s2 ms [Branch (JAL (n2w 0, w2w (word_lsr a 1)))] Hs Hr); [discriminate| |].
    + cbn [run_ok]. split; [reflexivity|split; [exact Hb0|split; [exact Logic.I|split; [exact Logic.I|]]]].
      cbn [aexec apc A0_of riscv_targetProof.A0_of]. rewrite near21 by assumption. apply aligned_add; assumption.
    + unfold QA_of; cbn [arun aexec aregs apc amem A0_of riscv_targetProof.A0_of]. rewrite near21 by assumption.
      rewrite <- Hasm. cbn [asmSem.asm jump_to_offset upd_pc set_pc pc mem regs]. split; [reflexivity|split; [reflexivity|]].
      intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3 & H4 & H5). regs_simp. apply Hg; lia.
  - assert (Hl : riscv_ast (Jump a) = [ArithI (AUIPC (temp_reg, word_extract 31 12 (word_sub a (sw2sw (word_extract 11 0 a : word12))) : word20));
         Branch (JALR (n2w 0, temp_reg, word_extract 11 0 a : word12))]) by (cbn [riscv_ast]; rewrite Er; reflexivity).
    rewrite Hl in Hb. apply bytes1 in Hb as [Hb0 Hb]. apply bytes1 in Hb as [Hb1 _].
    assert (Hlen : LENGTH (riscv_enc (Jump a)) = 8) by (rewrite riscv_enc_flat, Hl; reflexivity).
    assert (Ht : word_and (word_add (word_add s1.(pc) (sw2sw (word_concat (word_extract 31 12 (word_sub a (sw2sw (word_extract 11 0 a : word12))) : word20) (n2w 0 : word12) : word32)))
                    (sw2sw (word_extract 11 0 a : word12))) (sw2sw (n2w 2 : word2)) = word_add s1.(pc) a).
    { rewrite <- lemmas.WORD_ADD_ASSOC, hi_lo by exact Hw. apply and_m2.
      apply (word_bit0_aligned _ 2); [apply aligned_add; assumption|lia]. }
    unfold A0_of in *.
  apply (enc_sim s1 _ s2 ms (riscv_ast (Jump a)) Hs Hr); rewrite Hl; [discriminate| |].
    + cbn [run_ok]. split; [split; [reflexivity|split; [exact Hb0|split; [exact Logic.I|split; [exact Logic.I|]]]]|split].
      * cbn [aexec apc A0_of riscv_targetProof.A0_of]. apply (aligned_add4 _ 1), Hal.
      * split; [reflexivity|]. cbn [aexec apc A0_of riscv_targetProof.A0_of]. exact (pcs_in (Jump a) _ 1 ltac:(rewrite Hlen; lia)).
      * split; [reflexivity|split; [exact Hb1|split; [exact Logic.I|split; [exact Logic.I|]]]].
        cbn [aexec apc aregs A0_of riscv_targetProof.A0_of]. unfold temp_reg. regs_simp. rewrite Ht. apply aligned_add; assumption.
    + unfold QA_of; cbn [arun aexec aregs apc amem A0_of riscv_targetProof.A0_of]. unfold temp_reg. regs_simp. rewrite Ht.
      rewrite <- Hasm. cbn [asmSem.asm jump_to_offset upd_pc set_pc pc mem regs]. split; [reflexivity|split; [reflexivity|]].
      intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3 & H4 & H5). regs_simp. apply Hg; lia.
Qed.

Lemma sim_call s1 s2 ms a :
  asm_step riscv_config s1 (Call a) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (Call a) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  pose proof Hs as (Hb & Hlr & _). cbn [link_reg riscv_config] in Hlr.
  cbn [asm_ok] in Hok. apply Bool.andb_true_iff in Hok as [_ Hok]. apply jump_off_ok in Hok as [Hw Ha].
  rewrite riscv_enc_flat in Hb.
  destruct (word_le min21 a && word_le a max21)%bool eqn:Er.
  - assert (Hl : riscv_ast (Call a) = [Branch (JAL (n2w 1, w2w (word_lsr a 1)))]) by (cbn [riscv_ast]; rewrite Er; reflexivity).
    assert (Hlen : LENGTH (riscv_enc (Call a)) = 4) by (rewrite riscv_enc_flat, Hl; reflexivity).
    rewrite Hl in Hb. apply bytes1 in Hb as [Hb0 _].
    unfold A0_of in *.
  apply (enc_sim s1 _ s2 ms [Branch (JAL (n2w 1, w2w (word_lsr a 1)))] Hs Hr); [discriminate| |].
    + cbn [run_ok]. split; [reflexivity|split; [exact Hb0|split; [exact Logic.I|split; [exact Logic.I|]]]].
      cbn [aexec apc A0_of riscv_targetProof.A0_of]. rewrite near21 by assumption. apply aligned_add; assumption.
    + unfold QA_of; cbn [arun aexec aregs apc amem A0_of riscv_targetProof.A0_of]. rewrite near21 by assumption.
      rewrite <- Hasm, Hlen. cbn [asmSem.asm jump_to_offset upd_pc upd_reg set_regs set_pc pc mem regs lr].
      rewrite Hlr. split; [reflexivity|split; [reflexivity|]].
      intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3 & H4 & H5). regs_simp. fin_regs Hg.
  - assert (Hl : riscv_ast (Call a) = [ArithI (AUIPC (n2w 1, word_extract 31 12 (word_sub a (sw2sw (word_extract 11 0 a : word12))) : word20));
         Branch (JALR (n2w 1, n2w 1, word_extract 11 0 a : word12))]) by (cbn [riscv_ast]; rewrite Er; reflexivity).
    rewrite Hl in Hb. apply bytes1 in Hb as [Hb0 Hb]. apply bytes1 in Hb as [Hb1 _].
    assert (Hlen : LENGTH (riscv_enc (Call a)) = 8) by (rewrite riscv_enc_flat, Hl; reflexivity).
    assert (Ht : word_and (word_add (word_add s1.(pc) (sw2sw (word_concat (word_extract 31 12 (word_sub a (sw2sw (word_extract 11 0 a : word12))) : word20) (n2w 0 : word12) : word32)))
                    (sw2sw (word_extract 11 0 a : word12))) (sw2sw (n2w 2 : word2)) = word_add s1.(pc) a).
    { rewrite <- lemmas.WORD_ADD_ASSOC, hi_lo by exact Hw. apply and_m2.
      apply (word_bit0_aligned _ 2); [apply aligned_add; assumption|lia]. }
    unfold A0_of in *.
  apply (enc_sim s1 _ s2 ms (riscv_ast (Call a)) Hs Hr); rewrite Hl; [discriminate| |].
    + cbn [run_ok]. split; [split; [reflexivity|split; [exact Hb0|split; [exact Logic.I|split; [exact Logic.I|]]]]|split].
      * cbn [aexec apc A0_of riscv_targetProof.A0_of]. apply (aligned_add4 _ 1), Hal.
      * split; [reflexivity|]. cbn [aexec apc A0_of riscv_targetProof.A0_of]. exact (pcs_in (Call a) _ 1 ltac:(rewrite Hlen; lia)).
      * split; [reflexivity|split; [exact Hb1|split; [exact Logic.I|split; [exact Logic.I|]]]].
        cbn [aexec apc aregs A0_of riscv_targetProof.A0_of]. regs_simp. rewrite Ht. apply aligned_add; assumption.
    + unfold QA_of; cbn [arun aexec aregs apc amem A0_of riscv_targetProof.A0_of]. regs_simp. rewrite Ht.
      rewrite <- Hasm, Hlen. cbn [asmSem.asm jump_to_offset upd_pc upd_reg set_regs set_pc pc mem regs lr].
      rewrite Hlr. split; [reflexivity|split; [reflexivity|]].
      intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3 & H4 & H5). regs_simp. fin_regs Hg.
      rewrite add_n2w_add. reflexivity.
Qed.

Lemma sim_jumpreg s1 s2 ms r :
  asm_step riscv_config s1 (JumpReg r) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (JumpReg r) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  pose proof Hs as (Hb & _ & _ & Halign & _). cbn [code_alignment riscv_config] in Halign.
  cbn [asm_ok] in Hok. apply reg_ok_iff in Hok.
  assert (Har : aligned 2 (s1.(regs) r) = true).
  { rewrite <- Hasm in Hf. cbn [asmSem.asm upd_pc set_pc assert set_failed failed read_reg] in Hf.
    rewrite Halign in Hf. apply Bool.orb_false_iff in Hf as [Hf _]. apply Bool.negb_false_iff in Hf. exact Hf. }
  rewrite riscv_enc_flat in Hb. cbn [riscv_ast] in Hb. apply bytes1 in Hb as [Hb0 _].
  assert (Ht : word_and (word_add (rreg (riscv_targetProof.gregs (embedriscv_state ms)) (n2w r)) (sw2sw (n2w 0 : word12))) (sw2sw (n2w 2 : word2)) = s1.(regs) r).
  { regs_simp. rewrite Hg by lia. change (sw2sw (n2w 0 : word12) : word64) with (n2w 0 : word64).
    rewrite add_n2w_0. apply and_m2. apply (word_bit0_aligned _ 2); [exact Har|lia]. }
  unfold A0_of in *.
  apply (enc_sim s1 _ s2 ms (riscv_ast (JumpReg r)) Hs Hr); cbn [riscv_ast]; [discriminate| |].
  - cbn [run_ok]. split; [reflexivity|split; [exact Hb0|split; [exact Logic.I|split; [exact Logic.I|]]]].
    cbn [aexec apc aregs A0_of riscv_targetProof.A0_of]. rewrite Ht. exact Har.
  - unfold QA_of; cbn [arun aexec aregs apc amem A0_of riscv_targetProof.A0_of]. rewrite Ht.
    rewrite <- Hasm. cbn [asmSem.asm upd_pc set_pc assert set_failed pc mem regs read_reg].
    split; [reflexivity|split; [reflexivity|]].
    intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3 & H4 & H5). regs_simp. apply Hg; lia.
Qed.

(** ** Conditional jumps (Galette-only) *)

(** ** Conditional jumps *)

Lemma ge_lt (x y : word64) : word_ge x y = negb (word_lt x y).
Proof. rewrite word_ge_Z, word_lt_Z. destruct (Z.leb_spec (w2i y) (w2i x)), (Z.ltb_spec (w2i x) (w2i y)); auto; lia. Qed.

Lemma hs_lo (x y : word64) : word_hs x y = negb (word_lo x y).
Proof. rewrite lemmas.word_hs_w2n, lemmas.word_lo_w2n. destruct (N.leb_spec (w2n y) (w2n x)), (N.ltb_spec (w2n x) (w2n y)); auto; lia. Qed.

Lemma add_sub_k (pc a : word64) k : word_add (word_add pc (n2w k)) (word_sub a (n2w k)) = word_add pc a.
Proof.
  rewrite <- lemmas.WORD_ADD_ASSOC. f_equal. rewrite lemmas.WORD_ADD_COMM. apply lemmas.WORD_SUB_ADD.
Qed.

Lemma near_range (a : word64) : (word_le (word_2comp (n2w 4092)) a && word_le a (n2w 4095))%bool = true ->
  (-4092 <= w2i a <= 4095)%Z.
Proof.
  intros H. apply Bool.andb_true_iff in H as [H1 H2]. apply word_le_w2i in H1, H2.
  change (w2i (word_2comp (n2w 4092) : word64)) with (-4092)%Z in H1.
  change (w2i (n2w 4095 : word64)) with 4095%Z in H2. lia.
Qed.

Lemma cjump_ok (a : word64) : cjump_offset_ok riscv_config a = true ->
  (-1048568 <= w2i a <= 1048579)%Z /\ aligned 2 a = true.
Proof.
  unfold cjump_offset_ok, offset_ok; cbn [riscv_config cjump_offset code_alignment].
  rewrite !Bool.andb_true_iff. intros ((H1 & H2) & H3). apply word_le_w2i in H1, H2.
  change (w2i (word_add min21 (n2w 8))) with (-1048568)%Z in H1.
  change (w2i (word_add max21 (n2w 4))) with 1048579%Z in H2. auto.
Qed.

Lemma half_bounds (A : Z) lo hi : (lo <= A <= hi)%Z -> (lo / 2 <= A / 2 <= hi / 2)%Z.
Proof. intros [H1 H2]. split; apply Z.div_le_mono; lia. Qed.

Lemma off12_0 (a : word64) : (-4092 <= w2i a <= 4095)%Z -> aligned 2 a = true ->
  word_lsl (sw2sw (w2w (word_lsr a 1) : word12) : word64) 1 = a.
Proof.
  intros H Ha. apply branch_off0; [vm_compute; discriminate|apply aligned_2_1, Ha|].
  apply half_bounds in H. change (INT_MIN 12) with (-2048)%Z. change (INT_MAX 12) with 2047%Z. cbn in H. lia.
Qed.

Lemma off12_2 (a : word64) : (-4092 <= w2i a <= 4095)%Z -> aligned 2 a = true ->
  word_lsl (sw2sw (word_sub (w2w (word_lsr a 1) : word12) (n2w 2)) : word64) 1 = word_sub a (n2w 4).
Proof.
  intros H Ha. apply (branch_off a 2); [vm_compute; discriminate|apply aligned_2_1, Ha|].
  apply half_bounds in H. change (INT_MIN 12) with (-2048)%Z. change (INT_MAX 12) with 2047%Z. cbn in H. lia.
Qed.

Lemma off20 (a : word64) c : (-1048568 <= w2i a <= 1048579)%Z -> aligned 2 a = true -> 2 <= c <= 4 ->
  word_lsl (sw2sw (word_sub (w2w (word_lsr a 1) : word20) (n2w c)) : word64) 1 = word_sub a (n2w (2 * c)).
Proof.
  intros H Ha Hc. apply (branch_off a c); [vm_compute; discriminate|apply aligned_2_1, Ha|].
  apply half_bounds in H. change (INT_MIN 20) with (-524288)%Z. change (INT_MAX 20) with 524287%Z. cbn in H. lia.
Qed.

Lemma imm_cmp_ok c (i : word64) : reg_imm_ok (inr c) (Imm i) riscv_config = true -> (-2048 <= w2i i <= 2047)%Z.
Proof.
  unfold reg_imm_ok, valid_imm; cbn [riscv_config]. rewrite Bool.orb_true_iff, !Bool.andb_true_iff.
  intros [[Hx _]|[Hlo Hhi]]; [discriminate Hx|].
  change (bool_decide (inr c = inl Sub)) with false in Hlo. apply word_le_w2i in Hlo, Hhi.
  rewrite w2i_min12 in Hlo. rewrite w2i_max12 in Hhi. lia.
Qed.

Lemma sub_sub_n2w {n : N} (x : word n) p q : word_sub (word_sub x (n2w p)) (n2w q) = word_sub x (n2w (p + q)).
Proof. rewrite <- lemmas.WORD_SUB_PLUS, lemmas.word_add_n2w. reflexivity. Qed.

Lemma add_n2w_44 (pc : word64) : word_add (word_add pc (n2w 4)) (n2w 4) = word_add pc (n2w 8).
Proof. apply add_n2w_add. Qed.

Lemma add_n2w_c (x : word64) a b c : a + b = c -> word_add (word_add x (n2w a)) (n2w b) = word_add x (n2w c).
Proof. intros <-. apply add_n2w_add. Qed.

Ltac addr_norm :=
  repeat match goal with
  | H : context [word_add (word_add ?x (n2w ?a)) (n2w ?b)] |- _ =>
      is_lit a; is_lit b; let c := eval vm_compute in (a + b) in rewrite (add_n2w_c x a b c eq_refl) in H
  | |- context [word_add (word_add ?x (n2w ?a)) (n2w ?b)] =>
      is_lit a; is_lit b; let c := eval vm_compute in (a + b) in rewrite (add_n2w_c x a b c eq_refl)
  end.

Lemma sub_sub_c {n : N} (x : word n) p q c : p + q = c -> word_sub (word_sub x (n2w p)) (n2w q) = word_sub x (n2w c).
Proof. intros <-. apply sub_sub_n2w. Qed.

Ltac sub_norm :=
  repeat match goal with
  | |- context [word_sub (word_sub ?x (n2w ?a)) (n2w ?b)] =>
      is_lit a; is_lit b; let c := eval vm_compute in (a + b) in rewrite (sub_sub_c x a b c eq_refl)
  | H : context [word_sub (word_sub ?x (n2w ?a)) (n2w ?b)] |- _ =>
      is_lit a; is_lit b; let c := eval vm_compute in (a + b) in rewrite (sub_sub_c x a b c eq_refl) in H
  | |- context [n2w (2 * ?c)] => is_lit c; let v := eval vm_compute in (2 * c) in change (2 * c) with v
  end.

Ltac solve_sp :=
  lazymatch goal with
  | |- _ /\ _ => split; solve_sp
  | |- true = true => reflexivity
  | |- True => exact Logic.I
  | |- bytes_in_memory _ _ _ _ => assumption
  | |- aligned 2 (word_add (pc _) (n2w 4)) = true => apply (aligned_add4 _ 1); assumption
  | |- aligned 2 (word_add (pc _) (n2w 8)) = true => apply (aligned_add4 _ 2); assumption
  | |- aligned 2 (word_add (pc _) (n2w 12)) = true => apply (aligned_add4 _ 3); assumption
  | |- aligned 2 (word_add (pc _) _) = true => apply aligned_add; assumption
  | |- mem ?s = mem ?s => reflexivity
  | |- word_add _ (n2w 4) IN all_pcs _ _ 2 => apply (pcs_in _ _ 1); match goal with H : LENGTH (riscv_enc _) = _ |- _ => rewrite H end; reflexivity
  | |- word_add _ (n2w 8) IN all_pcs _ _ 2 => apply (pcs_in _ _ 2); match goal with H : LENGTH (riscv_enc _) = _ |- _ => rewrite H end; reflexivity
  | |- _ => idtac
  end.

Ltac jc_qa Hlen Hg :=
  first [ reflexivity
        | rewrite Hlen; reflexivity
        | intros ? ?; reflexivity
        | let r := fresh "r" in let H0 := fresh "H0" in let Hav := fresh "Hav" in
          intros r H0 Hav; apply avoid_iff in Hav as (? & ? & ? & ? & ?); regs_simp; apply Hg; lia
        | idtac ].

Ltac jc_prep Hs Hr :=
  let Hal := fresh "Hal" in let Hbe := fresh "Hbe" in let Hasm := fresh "Hasm" in
  let Hf := fresh "Hf" in let Hok := fresh "Hok" in let Hg := fresh "Hg" in
  destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).

Lemma sim_jc_reg s1 s2 ms c r1 r2 a :
  asm_step riscv_config s1 (JumpCmp c r1 (Reg r2) a) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (JumpCmp c r1 (Reg r2) a) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  pose proof Hs as (Hb & _).
  cbn [asm_ok] in Hok. apply Bool.andb_true_iff in Hok as [Hoff Hok].
  unfold cmp_ok, reg_imm_ok in Hok.
  apply cjump_ok in Hoff as [Hw Ha]. and_facts Hok.
  rewrite riscv_enc_flat in Hb.
  destruct (word_le (word_2comp (n2w 4092)) a && word_le a (n2w 4095))%bool eqn:Er.
  - pose proof (near_range a Er) as Hn.
    destruct c.
    all: unfold A0_of in *.
  all: match goal with |- enc_goal _ ?ii _ _ =>
           eassert (Hl : riscv_ast ii = _) by (cbn [riscv_ast]; rewrite Er; reflexivity);
           assert (Hlen : LENGTH (riscv_enc ii) = 4 * LENGTH (riscv_ast ii))
             by (rewrite riscv_enc_flat; apply LENGTH_FLAT_encode) end.
    all: rewrite Hl in Hb, Hlen; cbn [LENGTH] in Hlen; repeat (apply bytes1 in Hb as [? Hb]); rewrite ?add_n2w_44 in *.
    all: cbn [N.succ N.mul] in Hlen.
    all: unfold A0_of in *.
  all: match goal with |- enc_goal _ (JumpCmp ?cc _ _ _) _ _ =>
           destruct (word_cmp cc (s1.(regs) r1) (s1.(regs) r2)) eqn:Ec end.
    all: unfold A0_of in *.
  all: match goal with |- enc_goal _ ?ii _ _ => unfold A0_of in *; apply (enc_sim s1 _ s2 ms (riscv_ast ii) Hs Hr); rewrite Hl; [discriminate| |] end.
    all: cbn [run_ok arun]; unfold step_pre, QA_of, PA_of;
         cbn [aexec aregs apc amem A0_of riscv_targetProof.A0_of mem_ok acc_ok supported]; unfold temp_reg; regs_simp; rewrite ?Hg by lia.
    all: rewrite ?ge_lt, ?hs_lo; cbn [word_cmp] in Ec; rewrite ?Ec; cbv iota.
    all: rewrite ?off12_0, ?off12_2 by assumption; rewrite ?add_sub_k, ?add_n2w_44.
    all: solve_sp.
    all: try (rewrite <- Hasm; unfold asmSem.asm, reg_imm, read_reg; cbn [word_cmp]; rewrite Ec;
         cbn [jump_to_offset upd_pc set_pc pc mem regs]).
    all: solve_sp.
    all: jc_qa Hlen Hg.
  - destruct c.
    all: unfold A0_of in *.
  all: match goal with |- enc_goal _ ?ii _ _ =>
           eassert (Hl : riscv_ast ii = _) by (cbn [riscv_ast]; rewrite Er; reflexivity);
           assert (Hlen : LENGTH (riscv_enc ii) = 4 * LENGTH (riscv_ast ii))
             by (rewrite riscv_enc_flat; apply LENGTH_FLAT_encode) end.
    all: rewrite Hl in Hb, Hlen; cbn [LENGTH] in Hlen; repeat (apply bytes1 in Hb as [? Hb]); addr_norm.
    all: cbn [N.succ N.mul] in Hlen.
    all: unfold A0_of in *.
  all: match goal with |- enc_goal _ (JumpCmp ?cc _ _ _) _ _ =>
           destruct (word_cmp cc (s1.(regs) r1) (s1.(regs) r2)) eqn:Ec end.
    all: unfold A0_of in *.
  all: match goal with |- enc_goal _ ?ii _ _ =>
         lazymatch goal with
         | |- context [JumpCmp NotEqual _ _ _] => idtac
         | |- context [JumpCmp NotLess _ _ _] => idtac
         | |- context [JumpCmp NotLower _ _ _] => idtac
         | |- context [JumpCmp NotTest _ _ _] => idtac
         | _ => idtac end;
         lazymatch type of Ec with
         | _ = true => apply (enc_sim s1 _ s2 ms (riscv_ast ii) Hs Hr); rewrite Hl; [discriminate| |]
         | _ = false => apply (enc_sim s1 _ s2 ms (removelast (riscv_ast ii)) Hs Hr); rewrite Hl; cbn [removelast]; [discriminate| |]
         end end.
    all: cbn [word_cmp] in Ec;
         try lazymatch type of Ec with
             | negb _ = true => apply Bool.negb_true_iff in Ec
             | negb _ = false => apply Bool.negb_false_iff in Ec end.
    all: cbn [run_ok arun]; unfold step_pre, QA_of, PA_of;
         cbn [aexec aregs apc amem A0_of riscv_targetProof.A0_of mem_ok acc_ok supported]; unfold temp_reg; regs_simp; rewrite ?Hg by lia.
    all: rewrite ?ge_lt, ?hs_lo; rewrite ?Ec; cbn [negb]; cbv iota.
    all: sub_norm; rewrite ?(off20 a 2), ?(off20 a 4) by (first [assumption|lia]); sub_norm.
    all: try change (word_lsl (sw2sw (n2w 4 : word12) : word64) 1) with (n2w 8 : word64).
    all: rewrite ?add_sub_k; addr_norm; rewrite ?add_sub_k.
    all: solve_sp.
    all: try (rewrite <- Hasm; unfold asmSem.asm, reg_imm, read_reg; cbn [word_cmp]; rewrite ?Ec; cbn [negb];
         cbn [jump_to_offset upd_pc set_pc pc mem regs]).
    all: solve_sp.
    all: jc_qa Hlen Hg.
Qed.

Lemma sim_jc_imm s1 s2 ms c r1 i a :
  asm_step riscv_config s1 (JumpCmp c r1 (Imm i) a) s2 -> target_state_rel riscv_target s1 ms ->
  enc_goal s1 (JumpCmp c r1 (Imm i) a) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  pose proof Hs as (Hb & _).
  cbn [asm_ok] in Hok. apply Bool.andb_true_iff in Hok as [Hoff Hok].
  unfold cmp_ok, reg_imm_ok in Hok.
  apply cjump_ok in Hoff as [Hw Ha]. apply Bool.andb_true_iff in Hok as [Hok Hi].
  apply imm_cmp_ok in Hi. apply reg_ok_iff in Hok.
  rewrite riscv_enc_flat in Hb.
  destruct (word_le (word_2comp (n2w 4092)) a && word_le a (n2w 4095))%bool eqn:Er.
  - pose proof (near_range a Er) as Hn.
    destruct c.
    all: unfold A0_of in *.
  all: match goal with |- enc_goal _ ?ii _ _ =>
           eassert (Hl : riscv_ast ii = _) by (cbn [riscv_ast]; rewrite Er; reflexivity);
           assert (Hlen : LENGTH (riscv_enc ii) = 4 * LENGTH (riscv_ast ii))
             by (rewrite riscv_enc_flat; apply LENGTH_FLAT_encode) end.
    all: rewrite Hl in Hb, Hlen; cbn [LENGTH] in Hlen; repeat (apply bytes1 in Hb as [? Hb]); rewrite ?add_n2w_44 in *.
    all: cbn [N.succ N.mul] in Hlen.
    all: unfold A0_of in *.
  all: match goal with |- enc_goal _ (JumpCmp ?cc _ _ _) _ _ =>
           destruct (word_cmp cc (s1.(regs) r1) i) eqn:Ec end.
    all: unfold A0_of in *.
  all: match goal with |- enc_goal _ ?ii _ _ => unfold A0_of in *; apply (enc_sim s1 _ s2 ms (riscv_ast ii) Hs Hr); rewrite Hl; [discriminate| |] end.
    all: cbn [run_ok arun]; unfold step_pre, QA_of, PA_of;
         cbn [aexec aregs apc amem A0_of riscv_targetProof.A0_of mem_ok acc_ok supported]; unfold temp_reg; regs_simp; rewrite ?Hg by lia;
         rewrite ?imm12_id by exact Hi; rewrite ?(proj1 (proj2 (proj2 (lemmas.WORD_OR_CLAUSES _)))).
    all: rewrite ?ge_lt, ?hs_lo; cbn [word_cmp] in Ec; rewrite ?Ec; cbv iota.
    all: rewrite ?off12_0, ?off12_2 by assumption; rewrite ?add_sub_k, ?add_n2w_44.
    all: solve_sp.
    all: try (rewrite <- Hasm; unfold asmSem.asm, reg_imm, read_reg; cbn [word_cmp]; rewrite Ec;
         cbn [jump_to_offset upd_pc set_pc pc mem regs]).
    all: solve_sp.
    all: jc_qa Hlen Hg.
  - destruct c.
    all: unfold A0_of in *.
  all: match goal with |- enc_goal _ ?ii _ _ =>
           eassert (Hl : riscv_ast ii = _) by (cbn [riscv_ast]; rewrite Er; reflexivity);
           assert (Hlen : LENGTH (riscv_enc ii) = 4 * LENGTH (riscv_ast ii))
             by (rewrite riscv_enc_flat; apply LENGTH_FLAT_encode) end.
    all: rewrite Hl in Hb, Hlen; cbn [LENGTH] in Hlen; repeat (apply bytes1 in Hb as [? Hb]); addr_norm.
    all: cbn [N.succ N.mul] in Hlen.
    all: unfold A0_of in *.
  all: match goal with |- enc_goal _ (JumpCmp ?cc _ _ _) _ _ =>
           destruct (word_cmp cc (s1.(regs) r1) i) eqn:Ec end.
    all: unfold A0_of in *.
  all: match goal with |- enc_goal _ ?ii _ _ =>
         lazymatch goal with
         | |- context [JumpCmp NotEqual _ _ _] => idtac
         | |- context [JumpCmp NotLess _ _ _] => idtac
         | |- context [JumpCmp NotLower _ _ _] => idtac
         | |- context [JumpCmp NotTest _ _ _] => idtac
         | _ => idtac end;
         lazymatch type of Ec with
         | _ = true => apply (enc_sim s1 _ s2 ms (riscv_ast ii) Hs Hr); rewrite Hl; [discriminate| |]
         | _ = false => apply (enc_sim s1 _ s2 ms (removelast (riscv_ast ii)) Hs Hr); rewrite Hl; cbn [removelast]; [discriminate| |]
         end end.
    all: cbn [word_cmp] in Ec;
         try lazymatch type of Ec with
             | negb _ = true => apply Bool.negb_true_iff in Ec
             | negb _ = false => apply Bool.negb_false_iff in Ec end.
    all: cbn [run_ok arun]; unfold step_pre, QA_of, PA_of;
         cbn [aexec aregs apc amem A0_of riscv_targetProof.A0_of mem_ok acc_ok supported]; unfold temp_reg; regs_simp; rewrite ?Hg by lia;
         rewrite ?imm12_id by exact Hi; rewrite ?(proj1 (proj2 (proj2 (lemmas.WORD_OR_CLAUSES _)))).
    all: rewrite ?ge_lt, ?hs_lo; rewrite ?Ec; cbn [negb]; cbv iota.
    all: sub_norm; rewrite ?(off20 a 2), ?(off20 a 4) by (first [assumption|lia]); sub_norm.
    all: try change (word_lsl (sw2sw (n2w 4 : word12) : word64) 1) with (n2w 8 : word64).
    all: rewrite ?add_sub_k; addr_norm; rewrite ?add_sub_k.
    all: solve_sp.
    all: try (rewrite <- Hasm; unfold asmSem.asm, reg_imm, read_reg; cbn [word_cmp]; rewrite ?Ec; cbn [negb];
         cbn [jump_to_offset upd_pc set_pc pc mem regs]).
    all: solve_sp.
    all: jc_qa Hlen Hg.
Qed.

(** ** Encoding lengths (Galette-only) *)

Lemma sim_all s1 i s2 ms :
  asm_step riscv_config s1 i s2 -> target_state_rel riscv_target s1 ms -> enc_goal s1 i s2 ms.
Proof.
  intros Hs Hr.
  destruct i as [ii| a | c r ri a | a | r | r a].
  - destruct ii as [| r w | ar | m r [r2 w] | f].
    + apply sim_skip; assumption.
    + apply sim_const; assumption.
    + destruct ar as [b r1 r2 [r3|w]|sh r1 r2 [r3|w]|r1 r2 r3|r1 r2 r3 r4|r1 r2 r3 r4 r5|r1 r2 r3 r4|r1 r2 r3 r4|r1 r2 r3 r4].
      * apply sim_binop_reg; assumption.
      * apply sim_binop_imm; assumption.
      * apply sim_shift_reg; assumption.
      * apply sim_shift_imm; assumption.
      * apply sim_div; assumption.
      * apply sim_longmul; assumption.
      * exfalso. destruct (hyp_facts _ _ _ _ Hs Hr) as (_ & _ & _ & _ & Hok & _).
        cbn [asm_ok inst_ok arith_ok] in Hok. isa_simp Hok. discriminate Hok.
      * apply sim_addcarry; assumption.
      * apply sim_addoverflow; assumption.
      * apply sim_suboverflow; assumption.
    + apply sim_mem; assumption.
    + exfalso. destruct (hyp_facts _ _ _ _ Hs Hr) as (_ & _ & _ & _ & Hok & _).
      cbn [asm_ok inst_ok] in Hok. destruct f; cbn [fp_ok] in Hok; unfold fp_reg_ok in Hok;
        cbn [fp_reg_count riscv_config] in Hok; rewrite ?ltb0, ?Bool.andb_false_r in Hok; discriminate Hok.
  - apply sim_jump; assumption.
  - destruct ri; [apply sim_jc_reg|apply sim_jc_imm]; assumption.
  - apply sim_call; assumption.
  - apply sim_jumpreg; assumption.
  - apply sim_loc; assumption.
Qed.
Theorem reduced_riscv_encoder_correct : encoder_correct Configuration.riscvTarget.
Proof. split; [exact reduced_target_ok|].
 intros s1 i s2 ms [Hs Hr]; exact (sim_all s1 i s2 ms Hs Hr).
Qed.
