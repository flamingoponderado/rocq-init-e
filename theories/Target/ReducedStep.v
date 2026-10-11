(** Complete original reduced interpreter dispatch and outer step. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.Target Require Import ReducedTypes ReducedDecode ReducedStateOps
 ReducedMode ReducedUpperJump ReducedRegisterALU ReducedImmediateALU ReducedBranch
 ReducedSetLess ReducedShift ReducedMultiply ReducedDivide ReducedMemory ReducedLoad ReducedStore ReducedSignals.
Open Scope N_scope.
Definition Run (i : instruction) (s : riscv_state) : riscv_state :=
 match i with
 | ArithI x => match x with
   | ADDI args => dfnADDI args s
   | ADDIW args => dfnADDIW args s
   | ANDI args => dfnANDI args s
   | AUIPC args => dfnAUIPC args s
   | LUI args => dfnLUI args s
   | ORI args => dfnORI args s
   | SLTI args => dfnSLTI args s
   | SLTIU args => dfnSLTIU args s
   | XORI args => dfnXORI args s
   end
 | ArithR x => match x with
   | ADD args => dfnADD args s
   | AND args => dfnAND args s
   | OR args => dfnOR args s
   | SLT args => dfnSLT args s
   | SLTU args => dfnSLTU args s
   | SUB args => dfnSUB args s
   | XOR args => dfnXOR args s
   end
 | Branch x => match x with
   | BEQ args => dfnBEQ args s
   | BGE args => dfnBGE args s
   | BGEU args => dfnBGEU args s
   | BLT args => dfnBLT args s
   | BLTU args => dfnBLTU args s
   | BNE args => dfnBNE args s
   | JAL args => dfnJAL args s
   | JALR args => dfnJALR args s
   end
 | FENCE _ => s
 | Internal x => match x with
   | FETCH_FAULT args => dfnFETCH_FAULT args s
   | FETCH_MISALIGNED args => dfnFETCH_MISALIGNED args s
   end
 | Load x => match x with
   | LB args => dfnLB args s
   | LBU args => dfnLBU args s
   | LD args => dfnLD args s
   | LH args => dfnLH args s
   | LHU args => dfnLHU args s
   | LW args => dfnLW args s
   | LWU args => dfnLWU args s
   end
 | MulDiv x => match x with
   | DIV args => dfnDIV args s
   | DIVU args => dfnDIVU args s
   | MUL args => dfnMUL args s
   | MULH args => dfnMULH args s
   | MULHSU args => dfnMULHSU args s
   | MULHU args => dfnMULHU args s
   | REM args => dfnREM args s
   | REMU args => dfnREMU args s
   end
 | Shift x => match x with
   | SLL args => dfnSLL args s
   | SLLI args => dfnSLLI args s
   | SRA args => dfnSRA args s
   | SRAI args => dfnSRAI args s
   | SRL args => dfnSRL args s
   | SRLI args => dfnSRLI args s
   end
 | Store x => match x with
   | SB args => dfnSB args s
   | SD args => dfnSD args s
   | SH args => dfnSH args s
   | SW args => dfnSW args s
   end
 | System x => match x with
   | EBREAK => dfnEBREAK s
   | ECALL => dfnECALL s
   end
 | UnknownInstruction => dfnUnknownInstruction s
 end.
Definition DecodeAny (raw : rawInstType) : instruction :=
 match raw with Half h => ReducedDecode.DecodeRVC h | Word w => ReducedDecode.Decode w end.
Definition update_pc (pc : word 64) (s : riscv_state) : option riscv_state :=
 Some (riscv_state_c_PC_fupd (fun old => update (riscv_state_procID s) pc old) s).
Definition NextRISCV (state : riscv_state) : option riscv_state :=
 let '(raw,s) := Fetch state in
 let s := Run (DecodeAny raw) s in
 if negb (bool_decide (riscv_state_exception s = NoException)) then None else
 let pc := PC s in
 match NextFetch s with
 | None => update_pc (word_add pc (Skip s)) s
 | Some (BranchTo address) => update_pc address (writeNextFetch None s)
 | Some (Trap _) => None
 end.
