(** Agreement of the literal original decoder with a restriction of
    Galette's decoder, over every 32-bit encoding, not just compiler output. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words bitstring.
From Galette.HOL.examples.l3_machine_code.riscv.model Require Import riscv.
From InitE.Target Require Import Decode.
Open Scope N_scope.
Definition supportedInstruction (i : instruction) : bool :=
 match i with
 | riscv.Branch x => match x with
   | riscv.BEQ _ => true
   | riscv.BGE _ => true
   | riscv.BGEU _ => true
   | riscv.BLT _ => true
   | riscv.BLTU _ => true
   | riscv.BNE _ => true
   | riscv.JAL _ => true
   | riscv.JALR _ => true
   end
 | riscv.System x => match x with
   | riscv.EBREAK => true
   | riscv.ECALL => true
   | _ => false end
 | riscv.ArithI x => match x with
   | riscv.ADDI _ => true
   | riscv.ADDIW _ => true
   | riscv.ANDI _ => true
   | riscv.AUIPC _ => true
   | riscv.LUI _ => true
   | riscv.ORI _ => true
   | riscv.SLTI _ => true
   | riscv.SLTIU _ => true
   | riscv.XORI _ => true
   end
 | riscv.Shift x => match x with
   | riscv.SLL _ => true
   | riscv.SLLI _ => true
   | riscv.SRA _ => true
   | riscv.SRAI _ => true
   | riscv.SRL _ => true
   | riscv.SRLI _ => true
   | _ => false end
 | riscv.ArithR x => match x with
   | riscv.ADD _ => true
   | riscv.AND _ => true
   | riscv.OR _ => true
   | riscv.SLT _ => true
   | riscv.SLTU _ => true
   | riscv.SUB _ => true
   | riscv.XOR _ => true
   | _ => false end
 | riscv.MulDiv x => match x with
   | riscv.DIV _ => true
   | riscv.DIVU _ => true
   | riscv.MUL _ => true
   | riscv.MULH _ => true
   | riscv.MULHSU _ => true
   | riscv.MULHU _ => true
   | riscv.REM _ => true
   | riscv.REMU _ => true
   | _ => false end
 | riscv.Load x => match x with
   | riscv.LB _ => true
   | riscv.LBU _ => true
   | riscv.LD _ => true
   | riscv.LH _ => true
   | riscv.LHU _ => true
   | riscv.LW _ => true
   | riscv.LWU _ => true
   end
 | riscv.Store x => match x with
   | riscv.SB _ => true
   | riscv.SD _ => true
   | riscv.SH _ => true
   | riscv.SW _ => true
   end
 | riscv.FENCE _ => true
 | _ => false
 end.
Definition restrictInstruction (i : instruction) : instruction :=
 if supportedInstruction i then i else UnknownInstruction.
Lemma restrict_if (b : bool) (x y : instruction) :
 restrictInstruction (if b then x else y) =
 if b then restrictInstruction x else restrictInstruction y.
Proof. destruct b; reflexivity. Qed.
Theorem decoder_agreement (w : word32) :
 Decode.Decode w = restrictInstruction (riscv.Decode w).
Proof.
 unfold Decode.Decode, riscv.Decode, boolify32.
 cbn [word_bit dimindex].
 repeat rewrite restrict_if.
 cbn [restrictInstruction supportedInstruction].
 reflexivity.
Qed.
