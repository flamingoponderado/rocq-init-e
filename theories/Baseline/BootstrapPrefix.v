(** Symbolic original three-address-load prefix. The memory is arbitrary,
    allowing the later shared-input frame proof to reuse the same execution. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.relation Require Import relation.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem.
From InitE.Baseline Require Import BootstrapProgram BootstrapSteps BootstrapMemory.
From InitE.InitE Require Import Parameters BaselineArtifactLayout.
Open Scope N_scope.
Fixpoint runCode (instructions : list (asm.asm 64)) (s : asm_state 64) : asm_state 64 :=
 match instructions with [] => s | i::rest => runCode rest (after s i) end.
Definition prefixCode : list (asm.asm 64) := MAP snd (TAKE 3 bootstrapBlocks).
Theorem prefix_updates (s : asm_state 64) : pc s = n2w initialPc ->
 runCode prefixCode s =
 set_pc (n2w 0x80000018)
 (set_regs ((7 =+ n2w initDataEnd)
   ((6 =+ n2w initDataRam) ((5 =+ n2w initDataRom) (regs s)))) s).
Proof.
 destruct s as [rs fs memory domain pc0 link alignment endian failure].
 cbn [pc]; intro H; subst pc0.
 vm_compute; reflexivity.
Qed.

Lemma updateN_eqb {A : Type} r (value : A) f x :
 UPDATE r value f x = if x =? r then value else f x.
Proof.
 unfold UPDATE; destruct (decide (r=x)) as [E|E].
 - subst x; rewrite N.eqb_refl; reflexivity.
 - assert (H : (x =? r) = false) by (apply N.eqb_neq; congruence).
   rewrite H; reflexivity.
Qed.
Theorem prefix_endpoint : runCode prefixCode initialAsm = copyEntryAsm.
Proof.
 rewrite prefix_updates by reflexivity.
 unfold copyEntryAsm,initialAsm,set_pc,set_regs; cbn [regs].
 f_equal. apply functional_extensionality; intro r.
 rewrite !updateN_eqb.
 destruct (r =? 5) eqn:E5.
 - apply N.eqb_eq in E5; subst r; reflexivity.
 - destruct (r =? 6) eqn:E6.
   + apply N.eqb_eq in E6; subst r; reflexivity.
   + destruct (r =? 7); reflexivity.
Qed.

Fixpoint Checked (instructions : list (asm.asm 64)) (s : asm_state 64) : Prop :=
 match instructions with
 | [] => True
 | i::rest => asm_step riscv_target.riscv_config s i (after s i) /\ Checked rest (after s i)
 end.
Theorem checked_trace instructions s : Checked instructions s ->
 RTC (fun before after => exists i,
  asm_step riscv_target.riscv_config before i after) s (runCode instructions s).
Proof.
 revert s; induction instructions as [|i rest IH]; intros s H; cbn [runCode].
 - apply RTC_REFL.
 - destruct H as [Hstep Hrest]. eapply rtc_step.
   + exists i; exact Hstep.
   + apply IH; exact Hrest.
Qed.
