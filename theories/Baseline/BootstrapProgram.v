(** Software guest bootstrap encoded by the admitted RISC-V assembler. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From InitE.InitE Require Import BaselineArtifactLayout.
Open Scope N_scope.
Definition bootLoc (r pc address : N) : asm 64 := Loc r (n2w address-n2w pc)%w.
Definition bootConst (r value : N) : asm 64 := Inst (Const r (n2w value)).
Definition bootShift (r amount : N) : asm 64 := Inst (Arith (Shift Lsl r r (Imm (n2w amount)))).
Definition bootStore (r base offset : N) : asm 64 := Inst (Mem Store r (Addr base (n2w offset))).
Definition bootAdd (r : N) : asm 64 := Inst (Arith (Binop Add r r (Imm (n2w 8)))).
Definition bootstrapBlocks : list (N * asm 64) := [
 (0x80000000,bootLoc 5 0x80000000 initDataRom);
 (0x80000008,bootLoc 6 0x80000008 initDataRam);
 (0x80000010,bootLoc 7 0x80000010 initDataEnd);
 (0x80000018,Inst (Mem Load 28 (Addr 5 (n2w 0))));
 (0x8000001c,bootStore 28 6 0);
 (0x80000020,bootAdd 5);
 (0x80000024,bootAdd 6);
 (0x80000028,JumpCmp Lower 6 (Reg 7) (word_2comp (n2w 16)));
 (0x8000002c,bootLoc 5 0x8000002c initDataRam);
 (0x80000034,bootConst 6 161);
 (0x80000038,bootShift 6 24);
 (0x8000003c,bootStore 6 5 0);
 (0x80000040,bootLoc 5 0x80000040 (initDataRam+8));
 (0x80000048,bootConst 6 2015);
 (0x8000004c,bootShift 6 24);
 (0x80000050,bootStore 6 5 0);
 (0x80000054,bootLoc 5 0x80000054 (initDataRam+16));
 (0x8000005c,bootConst 6 63);
 (0x80000060,bootShift 6 29);
 (0x80000064,bootStore 6 5 0);
 (0x80000068,bootConst 5 161);
 (0x8000006c,bootShift 5 24);
 (0x80000070,bootLoc 6 0x80000070 (initDataRam+24));
 (0x80000078,bootStore 6 5 0);
 (0x8000007c,bootLoc 6 0x8000007c initDataEnd);
 (0x80000084,bootStore 6 5 8);
 (0x80000088,bootLoc 6 0x80000088 initDataEnd);
 (0x80000090,bootStore 6 5 16);
 (0x80000094,bootLoc 6 0x80000094 0x800f0134);
 (0x8000009c,bootStore 6 5 24);
 (0x800000a0,bootLoc 6 0x800000a0 0x800f1000);
 (0x800000a8,bootStore 6 5 32);
 (0x800000ac,bootConst 11 161);
 (0x800000b0,bootShift 11 24);
 (0x800000b4,bootConst 12 2015);
 (0x800000b8,bootShift 12 24);
 (0x800000bc,bootConst 13 63);
 (0x800000c0,bootShift 13 29);
 (0x800000c4,bootLoc 10 0x800000c4 nativePc);
 (0x800000cc,Jump (n2w nativePc-n2w 0x800000cc)%w)
].
Definition originalBootstrapBytes : list (word 8) := [n2w 151;n2w 34;n2w 15;n2w 0;n2w 147;n2w 130;n2w 2;n2w 0;n2w 23;n2w 3;n2w 2;n2w 32;n2w 19;n2w 3;n2w 131;n2w 255;n2w 151;n2w 147;n2w 2;n2w 32;n2w 147;n2w 131;n2w 3;n2w 254;n2w 3;n2w 190;n2w 2;n2w 0;n2w 35;n2w 48;n2w 195;n2w 1;n2w 147;n2w 130;n2w 130;n2w 0;n2w 19;n2w 3;n2w 131;n2w 0;n2w 227;n2w 104;n2w 115;n2w 254;n2w 151;n2w 2;n2w 2;n2w 32;n2w 147;n2w 130;n2w 66;n2w 253;n2w 19;n2w 99;n2w 16;n2w 10;n2w 19;n2w 19;n2w 131;n2w 1;n2w 35;n2w 176;n2w 98;n2w 0;n2w 151;n2w 2;n2w 2;n2w 32;n2w 147;n2w 130;n2w 130;n2w 252;n2w 19;n2w 99;n2w 240;n2w 125;n2w 19;n2w 19;n2w 131;n2w 1;n2w 35;n2w 176;n2w 98;n2w 0;n2w 151;n2w 2;n2w 2;n2w 32;n2w 147;n2w 130;n2w 194;n2w 251;n2w 19;n2w 99;n2w 240;n2w 3;n2w 19;n2w 19;n2w 211;n2w 1;n2w 35;n2w 176;n2w 98;n2w 0;n2w 147;n2w 98;n2w 16;n2w 10;n2w 147;n2w 146;n2w 130;n2w 1;n2w 23;n2w 3;n2w 2;n2w 32;n2w 19;n2w 3;n2w 131;n2w 250;n2w 35;n2w 176;n2w 98;n2w 0;n2w 23;n2w 147;n2w 2;n2w 32;n2w 19;n2w 3;n2w 67;n2w 247;n2w 35;n2w 180;n2w 98;n2w 0;n2w 23;n2w 147;n2w 2;n2w 32;n2w 19;n2w 3;n2w 131;n2w 246;n2w 35;n2w 184;n2w 98;n2w 0;n2w 23;n2w 3;n2w 15;n2w 0;n2w 19;n2w 3;n2w 3;n2w 10;n2w 35;n2w 188;n2w 98;n2w 0;n2w 23;n2w 19;n2w 15;n2w 0;n2w 19;n2w 3;n2w 3;n2w 246;n2w 35;n2w 176;n2w 98;n2w 2;n2w 147;n2w 101;n2w 16;n2w 10;n2w 147;n2w 149;n2w 133;n2w 1;n2w 19;n2w 102;n2w 240;n2w 125;n2w 19;n2w 22;n2w 134;n2w 1;n2w 147;n2w 102;n2w 240;n2w 3;n2w 147;n2w 150;n2w 214;n2w 1;n2w 23;n2w 21;n2w 0;n2w 0;n2w 19;n2w 5;n2w 197;n2w 250;n2w 111;n2w 0;n2w 80;n2w 122].
Theorem bootstrap_bytes_match :
 concat (MAP (fun block => riscv_target.riscv_enc (snd block)) bootstrapBlocks) = originalBootstrapBytes.
Proof. vm_compute; reflexivity. Qed.
Theorem bootstrap_instructions_admitted :
 EVERY (fun block => asm_ok (snd block) riscv_target.riscv_config) bootstrapBlocks = true.
Proof. vm_compute; reflexivity. Qed.
Definition initDataWords : N := (initDataEnd-initDataRam)/8.
Definition bootstrapSteps : N := 6+5*initDataWords+41.
Theorem original_bootstrap_step_count : initDataWords = 4606 /\ bootstrapSteps = 23077.
Proof. split; vm_compute; reflexivity. Qed.
