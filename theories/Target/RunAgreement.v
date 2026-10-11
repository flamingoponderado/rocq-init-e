(** Composition of reduced instruction simulations; stores supplied separately. *)
From Galette Require Import Base.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From InitE.Target Require Import ReducedTypes ReducedStep Configuration StateEmbedding StateAgreement
 InstructionEmbedding InstructionAgreement LoadAgreement SignalAgreement.
Theorem run_embedding_from_stores s i :
 Configuration.riscvOk s = true ->
 (forall st, embedriscv_state (ReducedStep.Run (ReducedTypes.Store st) s) =
 riscv.Run (riscv.Store (embedStore st)) (embedriscv_state s)) ->
 embedriscv_state (ReducedStep.Run i s) = riscv.Run (embedInstruction i) (embedriscv_state s).
Proof.
 intros H Hstores; pose proof (validity_native64 s H) as H64.
 destruct i as [ai|ar|br|fe|internal|load|md|shift|store|sys|].
 - destruct ai; repeat match goal with x : (_ * _)%type |- _ => destruct x end; cbn [ReducedStep.Run embedInstruction embedArithI embedArithR embedBranch embedInternal embedLoad embedMulDiv embedShift embedSystem riscv.Run fst snd].
   + apply simulate_ADDI.
   + apply simulate_ADDIW_64. exact H64.
   + apply simulate_ANDI.
   + apply simulate_AUIPC.
   + apply simulate_LUI.
   + apply simulate_ORI.
   + apply simulate_SLTI_64. exact H64.
   + apply simulate_SLTIU_64. exact H64.
   + apply simulate_XORI.
 - destruct ar; repeat match goal with x : (_ * _)%type |- _ => destruct x end; cbn [ReducedStep.Run embedInstruction embedArithI embedArithR embedBranch embedInternal embedLoad embedMulDiv embedShift embedSystem riscv.Run fst snd].
   + apply simulate_ADD.
   + apply simulate_AND.
   + apply simulate_OR.
   + apply simulate_SLT_64. exact H64.
   + apply simulate_SLTU_64. exact H64.
   + apply simulate_SUB.
   + apply simulate_XOR.
 - destruct br; repeat match goal with x : (_ * _)%type |- _ => destruct x end; cbn [ReducedStep.Run embedInstruction embedArithI embedArithR embedBranch embedInternal embedLoad embedMulDiv embedShift embedSystem riscv.Run fst snd].
   + apply simulate_BEQ_64. exact H64.
   + apply simulate_BGE_64. exact H64.
   + apply simulate_BGEU_64. exact H64.
   + apply simulate_BLT_64. exact H64.
   + apply simulate_BLTU_64. exact H64.
   + apply simulate_BNE_64. exact H64.
   + apply simulate_JAL.
   + apply simulate_JALR.
 - reflexivity.
 - destruct internal; cbn [ReducedStep.Run embedInstruction embedInternal riscv.Run]; [apply fetch_fault_embedding|apply fetch_misaligned_embedding].
 - destruct load; repeat match goal with x : (_ * _)%type |- _ => destruct x end; cbn [ReducedStep.Run embedInstruction embedArithI embedArithR embedBranch embedInternal embedLoad embedMulDiv embedShift embedSystem riscv.Run fst snd].
   + apply simulate_LB. exact H.
   + apply simulate_LBU. exact H.
   + apply simulate_LD. exact H.
   + apply simulate_LH. exact H.
   + apply simulate_LHU. exact H.
   + apply simulate_LW. exact H.
   + apply simulate_LWU. exact H.
 - destruct md; repeat match goal with x : (_ * _)%type |- _ => destruct x end; cbn [ReducedStep.Run embedInstruction embedArithI embedArithR embedBranch embedInternal embedLoad embedMulDiv embedShift embedSystem riscv.Run fst snd].
   + apply simulate_DIV.
   + apply simulate_DIVU_64. exact H64.
   + apply simulate_MUL.
   + apply simulate_MULH_64. exact H64.
   + apply simulate_MULHSU_64. exact H64.
   + apply simulate_MULHU_64. exact H64.
   + apply simulate_REM.
   + apply simulate_REMU.
 - destruct shift; repeat match goal with x : (_ * _)%type |- _ => destruct x end; cbn [ReducedStep.Run embedInstruction embedArithI embedArithR embedBranch embedInternal embedLoad embedMulDiv embedShift embedSystem riscv.Run fst snd].
   + apply simulate_SLL_64. exact H64.
   + apply simulate_SLLI_64. exact H64.
   + apply simulate_SRA_64. exact H64.
   + apply simulate_SRAI_64. exact H64.
   + apply simulate_SRL_64. exact H64.
   + apply simulate_SRLI_64. exact H64.
 - apply Hstores.
 - destruct sys; cbn [ReducedStep.Run embedInstruction embedSystem riscv.Run]; [apply breakpoint_embedding|apply environment_call_embedding].
 - apply unknown_embedding.
Qed.
