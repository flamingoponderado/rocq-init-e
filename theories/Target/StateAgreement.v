(** Basic compiler-model agreement for the actual reduced state. *)
From Galette Require Import Base.
From Stdlib Require Import Lia.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From Galette.cakeml.compiler.encoders.asm Require asmProps asmSem.
From InitE.Target Require Import ReducedTypes ReducedStateOps StateEmbedding Configuration.
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
