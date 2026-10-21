(** Original BootstrapMemory.lean: expected installed state is a definition
    to prove reachable, never a supplied challenge initialization condition. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.compiler.encoders.asm Require Import asmSem.
From InitE.Guest Require Import Basic Bookkeeping.
From InitE.InitE Require Import Parameters BaselineArtifactLayout SubmissionModel.
From InitE.Baseline Require Import Artifacts.
Open Scope N_scope.
Definition romMemory (a : word 64) : word 8 :=
 if (initialPc <=? w2n a) && (w2n a <? initialPc+LENGTH code)
 then nthN (w2n a-initialPc) code (n2w 0) else n2w 0.
Definition bootstrapDomain (a : word 64) : Prop :=
 submissionMemoryDomain a /\ forall i, i < 4 ->
 a <> (n2w nativePc-n2w (16*(i+1)))%w.
Definition initialAsm : asm_state 64 :=
 mk_asm_state (fun _ => n2w 0) (fun _ => n2w 0) romMemory bootstrapDomain
 (n2w initialPc) 1 2 false false.
Definition copyEntryAsm : asm_state 64 :=
 set_pc (n2w 0x80000018)
 (set_regs (fun r => if r =? 5 then n2w initDataRom
  else if r =? 6 then n2w initDataRam
  else if r =? 7 then n2w initDataEnd else n2w 0) initialAsm).
Definition wordByte (w : word 64) (offset : N) : word 8 :=
 n2w (w2n w / 2^(8*offset)).
Definition installedMemory (a : word 64) : word 8 :=
 if (sourceBase <=? w2n a) && (w2n a <? sourceBase+40) then
 wordByte (nthN ((w2n a-sourceBase)/8) startupHeaders (n2w 0)) ((w2n a-sourceBase) mod 8)
 else if (initDataRam <=? w2n a) && (w2n a <? initDataRam+24) then
 wordByte (nthN ((w2n a-initDataRam)/8)
 [n2w sourceBase;n2w stackStart;n2w ramEnd] (n2w 0)) ((w2n a-initDataRam) mod 8)
 else if (initDataRam+24 <=? w2n a) && (w2n a <? initDataEnd) then
 romMemory (n2w (initDataRom+w2n a-initDataRam)) else romMemory a.
Definition installedRegisters (r : N) : word 64 :=
 if r =? 10 then n2w nativePc
 else if r =? 11 then n2w sourceBase
 else if r =? 12 then n2w stackStart
 else if r =? 13 then n2w ramEnd
 else if r =? 5 then n2w sourceBase
 else if r =? 6 then n2w 0x800de000
 else if r =? 7 then n2w initDataEnd
 else if r =? 28 then nthN (LENGTH bitmaps-1) bitmaps (n2w 0)
 else n2w 0.
Definition installedAsm : asm_state 64 :=
 set_pc (n2w nativePc) (set_regs installedRegisters (set_mem installedMemory initialAsm)).
