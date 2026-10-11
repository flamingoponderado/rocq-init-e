(** Structural embedding of original reduced instructions into Galette. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From InitE.Target Require Import ReducedTypes ReducedDecode Decode.
Open Scope N_scope.
Definition embedArithI (x : ReducedTypes.ArithI_ty) : riscv.ArithI_ty :=
 match x with
 | ReducedTypes.ADDI args => riscv.ADDI (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.ADDIW args => riscv.ADDIW (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.ANDI args => riscv.ANDI (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.AUIPC args => riscv.AUIPC (fst (args), snd (args))
 | ReducedTypes.LUI args => riscv.LUI (fst (args), snd (args))
 | ReducedTypes.ORI args => riscv.ORI (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.SLTI args => riscv.SLTI (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.SLTIU args => riscv.SLTIU (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.XORI args => riscv.XORI (fst (args), fst (snd (args)), snd (snd (args)))
 end.
Definition embedArithR (x : ReducedTypes.ArithR_ty) : riscv.ArithR_ty :=
 match x with
 | ReducedTypes.ADD args => riscv.ADD (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.AND args => riscv.AND (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.OR args => riscv.OR (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.SLT args => riscv.SLT (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.SLTU args => riscv.SLTU (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.SUB args => riscv.SUB (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.XOR args => riscv.XOR (fst (args), fst (snd (args)), snd (snd (args)))
 end.
Definition embedBranch (x : ReducedTypes.Branch_ty) : riscv.Branch_ty :=
 match x with
 | ReducedTypes.BEQ args => riscv.BEQ (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.BGE args => riscv.BGE (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.BGEU args => riscv.BGEU (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.BLT args => riscv.BLT (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.BLTU args => riscv.BLTU (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.BNE args => riscv.BNE (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.JAL args => riscv.JAL (fst (args), snd (args))
 | ReducedTypes.JALR args => riscv.JALR (fst (args), fst (snd (args)), snd (snd (args)))
 end.
Definition embedInternal (x : ReducedTypes.Internal_ty) : riscv.Internal_ty :=
 match x with
 | ReducedTypes.FETCH_FAULT args => riscv.FETCH_FAULT args
 | ReducedTypes.FETCH_MISALIGNED args => riscv.FETCH_MISALIGNED args
 end.
Definition embedLoad (x : ReducedTypes.Load_ty) : riscv.Load_ty :=
 match x with
 | ReducedTypes.LB args => riscv.LB (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.LBU args => riscv.LBU (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.LD args => riscv.LD (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.LH args => riscv.LH (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.LHU args => riscv.LHU (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.LW args => riscv.LW (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.LWU args => riscv.LWU (fst (args), fst (snd (args)), snd (snd (args)))
 end.
Definition embedMulDiv (x : ReducedTypes.MulDiv_ty) : riscv.MulDiv_ty :=
 match x with
 | ReducedTypes.DIV args => riscv.DIV (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.DIVU args => riscv.DIVU (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.MUL args => riscv.MUL (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.MULH args => riscv.MULH (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.MULHSU args => riscv.MULHSU (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.MULHU args => riscv.MULHU (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.REM args => riscv.REM (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.REMU args => riscv.REMU (fst (args), fst (snd (args)), snd (snd (args)))
 end.
Definition embedShift (x : ReducedTypes.Shift_ty) : riscv.Shift_ty :=
 match x with
 | ReducedTypes.SLL args => riscv.SLL (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.SLLI args => riscv.SLLI (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.SRA args => riscv.SRA (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.SRAI args => riscv.SRAI (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.SRL args => riscv.SRL (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.SRLI args => riscv.SRLI (fst (args), fst (snd (args)), snd (snd (args)))
 end.
Definition embedStore (x : ReducedTypes.Store_ty) : riscv.Store_ty :=
 match x with
 | ReducedTypes.SB args => riscv.SB (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.SD args => riscv.SD (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.SH args => riscv.SH (fst (args), fst (snd (args)), snd (snd (args)))
 | ReducedTypes.SW args => riscv.SW (fst (args), fst (snd (args)), snd (snd (args)))
 end.
Definition embedSystem (x : ReducedTypes.System_ty) : riscv.System_ty :=
 match x with
 | ReducedTypes.EBREAK => riscv.EBREAK
 | ReducedTypes.ECALL => riscv.ECALL
 end.
Definition embedInstruction (i : ReducedTypes.instruction) : riscv.instruction :=
 match i with
 | ReducedTypes.ArithI args => riscv.ArithI (embedArithI args)
 | ReducedTypes.ArithR args => riscv.ArithR (embedArithR args)
 | ReducedTypes.Branch args => riscv.Branch (embedBranch args)
 | ReducedTypes.FENCE args => riscv.FENCE ((fst (args), fst (snd (args)), fst (snd (snd (args))), snd (snd (snd (args)))))
 | ReducedTypes.Internal args => riscv.Internal (embedInternal args)
 | ReducedTypes.Load args => riscv.Load (embedLoad args)
 | ReducedTypes.MulDiv args => riscv.MulDiv (embedMulDiv args)
 | ReducedTypes.Shift args => riscv.Shift (embedShift args)
 | ReducedTypes.Store args => riscv.Store (embedStore args)
 | ReducedTypes.System args => riscv.System (embedSystem args)
 | ReducedTypes.UnknownInstruction => riscv.UnknownInstruction
 end.
Lemma embed_instruction_if (b : bool) (x y : ReducedTypes.instruction) :
 embedInstruction (if b then x else y) = if b then embedInstruction x else embedInstruction y.
Proof. destruct b; reflexivity. Qed.
Theorem reduced_decoder_embedding (w : word 32) :
 embedInstruction (ReducedDecode.Decode w) = Decode.Decode w.
Proof.
 unfold ReducedDecode.Decode, Decode.Decode.
 repeat rewrite embed_instruction_if.
 cbn [embedInstruction embedArithI embedArithR embedBranch embedInternal embedLoad
      embedMulDiv embedShift embedStore embedSystem
      ReducedDecode.asImm12 ReducedDecode.asImm20 ReducedDecode.asSImm12
      riscv.asImm12 riscv.asImm20 riscv.asSImm12].
 reflexivity.
Qed.
