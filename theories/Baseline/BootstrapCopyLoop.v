(** Original five-instruction bitmap-copy loop; actual ASM execution. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From InitE.Baseline Require Import BootstrapProgram BootstrapSteps BootstrapPrefix BootstrapCopy BootstrapMemoryControl.
Open Scope N_scope.
Definition copyLoad : asm.asm 64 := Inst (Mem Load 28 (Addr 5 (n2w 0))).
Definition copyStore : asm.asm 64 := Inst (Mem Store 28 (Addr 6 (n2w 0))).
Definition copyLoopCode : list (asm.asm 64) :=
 [copyLoad;copyStore;bootAdd 5;bootAdd 6;JumpCmp Lower 6 (Reg 7) (word_2comp (n2w 16))].
Definition copyIteration (s : asm_state 64) := runCode copyLoopCode s.
Theorem copy_loop_original : copyLoopCode = MAP snd (TAKE 5 (DROP 3 bootstrapBlocks)).
Proof. reflexivity. Qed.
Theorem copy_loop_admitted :
 EVERY (fun i => asm_ok i riscv_target.riscv_config) copyLoopCode = true.
Proof. vm_compute; reflexivity. Qed.
Lemma upd_pc_current {a} p (s : asm_state a) : pc (upd_pc p s) = p.
Proof. reflexivity. Qed.
Lemma upd_pc_twice {a} p q (s : asm_state a) : upd_pc p (upd_pc q s) = upd_pc p s.
Proof. reflexivity. Qed.
Lemma after_copyLoad s : after s copyLoad =
 upd_pc (pc s+n2w 4)%w (mem_load 8 28 (Addr 5 (n2w 0)) s).
Proof. reflexivity. Qed.
Lemma after_copyStore s : after s copyStore =
 upd_pc (pc s+n2w 4)%w (mem_store 8 28 (Addr 6 (n2w 0)) s).
Proof. reflexivity. Qed.
Theorem copy_pair_after s : after (after s copyLoad) copyStore =
 upd_pc (pc s+n2w 8)%w (copyWord s).
Proof.
 rewrite after_copyStore,after_copyLoad,upd_pc_current,mem_store_upd_pc,upd_pc_twice.
 fold copyWord; rewrite <- WORD_ADD_ASSOC,word_add_n2w; reflexivity.
Qed.
