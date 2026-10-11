(** Reduced interpreter signals preserve the compiler model traps. *)
From Galette Require Import Base.
From Stdlib Require Import Lia.
Open Scope N_scope.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From InitE.Target Require Import ReducedTypes ReducedStateOps ReducedSignals StateEmbedding StateAgreement.
Theorem signal_exception_embedding s e :
 embedriscv_state (ReducedStateOps.signalException e s) =
 riscv.signalException (embedExceptionType e) (embedriscv_state s).
Proof. unfold ReducedStateOps.signalException,riscv.signalException; apply trap_embedding. Qed.
Theorem unknown_embedding s :
 embedriscv_state (dfnUnknownInstruction s) = riscv.dfn'UnknownInstruction (embedriscv_state s).
Proof. unfold dfnUnknownInstruction,riscv.dfn'UnknownInstruction; apply signal_exception_embedding. Qed.
Theorem breakpoint_embedding s :
 embedriscv_state (dfnEBREAK s) = riscv.dfn'EBREAK (embedriscv_state s).
Proof. unfold dfnEBREAK,riscv.dfn'EBREAK; apply signal_exception_embedding. Qed.
Theorem fetch_fault_embedding s address :
 embedriscv_state (dfnFETCH_FAULT address s) = riscv.dfn'FETCH_FAULT address (embedriscv_state s).
Proof. unfold dfnFETCH_FAULT,riscv.dfn'FETCH_FAULT; apply address_exception_embedding. Qed.
Theorem fetch_misaligned_embedding s address :
 embedriscv_state (dfnFETCH_MISALIGNED address s) = riscv.dfn'FETCH_MISALIGNED address (embedriscv_state s).
Proof. unfold dfnFETCH_MISALIGNED,riscv.dfn'FETCH_MISALIGNED; apply address_exception_embedding. Qed.

Lemma two_bit_cases (p : word 2) :
 p = n2w 0 \/ p = n2w 1 \/ p = n2w 2 \/ p = n2w 3.
Proof.
 pose proof (w2n_lt p) as H; change (w2n p < 4) in H.
 assert (w2n p=0 \/ w2n p=1 \/ w2n p=2 \/ w2n p=3) by lia.
 destruct H0 as [E|[E|[E|E]]]; rewrite <- (n2w_w2n p),E; auto.
Qed.
Theorem environment_call_embedding s :
 embedriscv_state (dfnECALL s) = riscv.dfn'ECALL (embedriscv_state s).
Proof.
 unfold dfnECALL,riscv.dfn'ECALL,riscv.signalEnvCall.
 change (embedriscv_state (signalException
 (match ReducedSignals.privilege (mstatus_MPRV (MachineCSR_mstatus (MCSR s))) with
 | User => UMode_Env_Call | Supervisor => SMode_Env_Call
 | Hypervisor => HMode_Env_Call | Machine => MMode_Env_Call end) s) =
 riscv.signalException
 (match riscv.privilege (mstatus_MPRV (MachineCSR_mstatus (MCSR s))) with
 | riscv.User => riscv.UMode_Env_Call | riscv.Supervisor => riscv.SMode_Env_Call
 | riscv.Hypervisor => riscv.HMode_Env_Call | riscv.Machine => riscv.MMode_Env_Call end)
 (embedriscv_state s)).
 rewrite signal_exception_embedding.
 destruct (two_bit_cases (mstatus_MPRV (MachineCSR_mstatus (MCSR s)))) as [E|[E|[E|E]]];
 rewrite E; vm_compute; reflexivity.
Qed.
