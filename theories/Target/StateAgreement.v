(** Basic compiler-model agreement for the actual reduced state. *)
From Galette Require Import Base.
From Stdlib Require Import Lia.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.combin Require combin.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From Galette.cakeml.compiler.encoders.asm Require asmProps asmSem.
From InitE.Target Require Import ReducedTypes ReducedStateOps ReducedUpperJump ReducedMemory ReducedMode StateEmbedding Configuration.
Open Scope N_scope.
Theorem gpr_embedding (s : ReducedTypes.riscv_state) (reg : word 5) :
 riscv.GPR reg (embedriscv_state s) = ReducedStateOps.GPR reg s.
Proof. reflexivity. Qed.
Theorem pc_embedding (s : ReducedTypes.riscv_state) :
 riscv.PC (embedriscv_state s) = ReducedTypes.riscv_state_c_PC s (ReducedTypes.riscv_state_procID s).
Proof. reflexivity. Qed.
Theorem memory_embedding (s : ReducedTypes.riscv_state) a :
 riscv.riscv_state_MEM8 (embedriscv_state s) a = ReducedTypes.riscv_state_MEM8 s a.
Proof. reflexivity. Qed.
Theorem validity_embedding (s : ReducedTypes.riscv_state) :
 riscv_target.riscv_ok (embedriscv_state s) = Configuration.riscvOk s.
Proof.
 unfold riscv_target.riscv_ok, Configuration.riscvOk, embedriscv_state.
 cbn.
 unfold embedMachineCSR,embedmstatus,embedmcpuid; cbn.
 destruct (ReducedTypes.riscv_state_c_NextFetch s (ReducedTypes.riscv_state_procID s)) as [control|].
 all: try destruct control.
 all: destruct (ReducedTypes.riscv_state_exception s); cbn [embedTransferControl embedSynchronousTrap embedExceptionType embedexception]; reflexivity.
Qed.
Theorem asm_relation_embedding (t : asmSem.asm_state 64) (s : ReducedTypes.riscv_state) :
 asmProps.target_state_rel Configuration.riscvTarget t s <->
 asmProps.target_state_rel riscv_target.riscv_target t (embedriscv_state s).
Proof.
 unfold asmProps.target_state_rel.
 cbn [Configuration.riscvTarget riscv_target.riscv_target].
 rewrite validity_embedding.
 cbn [embedriscv_state].
 split; intros (Hok & Hpc & Hmem & Hregs & Hfp).
 all: repeat split; try exact Hok; try exact Hpc; try exact Hmem; try exact Hregs.
 all: intros i Hi; change (i < 0) in Hi; lia.
Qed.
Lemma update_agreement {A B} `{EqDecision A} (key : A) (value : B) (f : A -> B) :
 ReducedStateOps.update key value f = combin.UPDATE key value f.
Proof.
 apply functional_extensionality; intro x.
 unfold ReducedStateOps.update,combin.UPDATE,bool_decide.
 destruct (decide (x = key)), (decide (key = x)); congruence.
Qed.
Theorem write_gpr_embedding (s : ReducedTypes.riscv_state) (reg : word 5) (value : word 64) :
 embedriscv_state (ReducedStateOps.writeGpr value reg s) =
 riscv.write'gpr (value,reg) (embedriscv_state s).
Proof.
 unfold ReducedStateOps.writeGpr,riscv.write'gpr,embedriscv_state.
 cbn; rewrite !update_agreement; reflexivity.
Qed.
Theorem write_GPR_embedding (s : ReducedTypes.riscv_state) (reg : word 5) (value : word 64) :
 embedriscv_state (ReducedStateOps.writeGPR value reg s) =
 riscv.write'GPR (value,reg) (embedriscv_state s).
Proof.
 unfold ReducedStateOps.writeGPR,riscv.write'GPR.
 destruct (negb (bool_decide (reg = n2w 0))); [apply write_gpr_embedding|reflexivity].
Qed.
Theorem write_next_fetch_embedding (s : ReducedTypes.riscv_state) (value : option ReducedTypes.TransferControl) :
 embedriscv_state (ReducedStateOps.writeNextFetch value s) =
 riscv.write'NextFetch (option_map embedTransferControl value) (embedriscv_state s).
Proof.
 unfold ReducedStateOps.writeNextFetch,riscv.write'NextFetch,embedriscv_state,
  riscv.riscv_state_c_NextFetch_fupd,ReducedTypes.riscv_state_c_NextFetch_fupd.
 cbn; f_equal.
 apply functional_extensionality; intro core.
 unfold ReducedStateOps.update,combin.UPDATE,bool_decide.
 destruct (decide (core = ReducedTypes.riscv_state_procID s)),
  (decide (ReducedTypes.riscv_state_procID s = core)); try congruence; reflexivity.
Qed.
Theorem branch_embedding (s : ReducedTypes.riscv_state) (pc : word 64) :
 embedriscv_state (ReducedUpperJump.branchTo pc s) = riscv.branchTo pc (embedriscv_state s).
Proof.
 unfold ReducedUpperJump.branchTo,riscv.branchTo.
 rewrite write_next_fetch_embedding; reflexivity.
Qed.
Theorem skip_embedding (s : ReducedTypes.riscv_state) :
 riscv.Skip (embedriscv_state s) = ReducedUpperJump.Skip s.
Proof. reflexivity. Qed.
Theorem write_skip_embedding (s : ReducedTypes.riscv_state) (value : word 64) :
 embedriscv_state (ReducedMemory.writeSkip value s) = riscv.write'Skip value (embedriscv_state s).
Proof.
 unfold ReducedMemory.writeSkip,riscv.write'Skip,embedriscv_state.
 cbn; rewrite update_agreement; reflexivity.
Qed.
Definition native64 (s : ReducedTypes.riscv_state) : Prop :=
 ReducedTypes.mcpuid_ArchBase (ReducedTypes.MachineCSR_mcpuid (ReducedStateOps.MCSR s)) = n2w 2.
Theorem reduced_mode64 (s : ReducedTypes.riscv_state) :
 native64 s -> ReducedMode.in32BitMode s = (false,s).
Proof.
 unfold native64,ReducedMode.in32BitMode,ReducedMode.curArch,ReducedMode.architecture.
 intros H; rewrite H; reflexivity.
Qed.
Theorem full_mode64 (s : ReducedTypes.riscv_state) :
 native64 s -> riscv.in32BitMode tt (embedriscv_state s) = (false,embedriscv_state s).
Proof.
 intros H; unfold riscv.in32BitMode,riscv.curArch,riscv.architecture,riscv.MCSR.
 cbn.
 unfold native64,ReducedStateOps.MCSR in H.
 rewrite H; reflexivity.
Qed.
Theorem validity_native64 (s : ReducedTypes.riscv_state) :
 Configuration.riscvOk s = true -> native64 s.
Proof.
 unfold Configuration.riscvOk,native64,ReducedStateOps.MCSR.
 rewrite !Bool.andb_true_iff.
 intros [[[[Hvm Harch] Hfetch] Hex] Hpc].
 apply (proj1 (bool_decide_spec _)); exact Harch.
Qed.
Theorem word_memory_embedding (s : ReducedTypes.riscv_state) (index : word 61) :
 riscv.MEM index (embedriscv_state s) = ReducedMemory.MEM index s.
Proof. unfold riscv.MEM,ReducedMemory.MEM; cbn beta iota zeta; rewrite !memory_embedding, (proj1 WORD_ADD_0); reflexivity. Qed.

Theorem trap_embedding (s : ReducedTypes.riscv_state) e badaddr :
 embedriscv_state (ReducedStateOps.setTrap e badaddr s) =
 riscv.setTrap (embedExceptionType e,badaddr) (embedriscv_state s).
Proof.
 unfold ReducedStateOps.setTrap,riscv.setTrap; rewrite write_next_fetch_embedding.
 unfold embedTransferControl,embedSynchronousTrap; cbn.
 unfold riscv.SynchronousTrap_badaddr_fupd,riscv.SynchronousTrap_trap_fupd; cbn.
 reflexivity.
Qed.
Theorem address_exception_embedding (s : ReducedTypes.riscv_state) e address :
 embedriscv_state (ReducedUpperJump.signalAddressException e address s) =
 riscv.signalAddressException (embedExceptionType e,address) (embedriscv_state s).
Proof. unfold ReducedUpperJump.signalAddressException,riscv.signalAddressException; apply trap_embedding. Qed.
