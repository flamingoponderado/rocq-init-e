(** Software precompile guest semantics with only host memory and terminal calls. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words alignment.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.string Require Import string.
From Galette.HOL.src.finite_maps Require Import finite_map.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.pancake.semantics Require panSem.
From Galette.cakeml.compiler.backend.proofs Require stack_removeProof.
From InitE.Guest Require Import Ast GasLimit ByteCodec Bookkeeping HostMemory.
From InitE.InitE Require Import Parameters.
Open Scope N_scope.
Open Scope hol_string_scope.
Definition sourceOracle : oracle HostMemory :=
 fun name host configuration bytes =>
 match name with
 | SharedMem op => sharedOracle op host configuration bytes
 | ExtCall _ => Oracle_final FFI_failed
 end.
Definition sourceFfi (input : InputBlob) : ffi_state HostMemory :=
 initial_ffi_state sourceOracle (guestHostMemory input).
Definition ordinaryDomain (address : word 64) : Prop :=
 stack_removeProof.addresses (n2w sourceBase) ((stackStart-sourceBase)/8-globalsWords) address.
Definition sharedDomain (address : word 64) : Prop :=
 aligned 3 address = true /\
 ((inputStart <= w2n address /\ w2n address < inputEnd) \/
  (outputStart <= w2n address /\ w2n address < outputEnd)).
Definition sourceMemory (address : word 64) : panSem.word_lab 64 :=
 let offset := w2n (address-n2w sourceBase)%w in
 panSem.Word (if (offset mod 8 =? 0) && (offset/8 <? LENGTH startupHeaders)
   then nth (N.to_nat (offset/8)) startupHeaders (n2w 0) else n2w 0).
Definition sourceInitialState (input : InputBlob) : panSem.state 64 HostMemory :=
 {| panSem.locals := FEMPTY; panSem.globals := FEMPTY; panSem.structs := [];
    panSem.code := FEMPTY; panSem.eshapes := FEMPTY;
    panSem.memory := sourceMemory; panSem.memaddrs := ordinaryDomain;
    panSem.sh_memaddrs := sharedDomain; panSem.clock := 0; panSem.be := false;
    panSem.ffi := sourceFfi input; panSem.base_addr := n2w sourceBase;
    panSem.top_addr := n2w heapEnd |}.
Definition sourceBehaviour (input : InputBlob) : behaviour :=
 panSem.semantics_decls (sourceInitialState input) (strlit "main") guestAst.
Example source_halt_terminal host configuration bytes :
 sourceOracle (ExtCall (strlit "halt")) host configuration bytes = Oracle_final FFI_failed.
Proof. reflexivity. Qed.
Example source_trap_terminal host configuration bytes :
 sourceOracle (ExtCall (strlit "trap")) host configuration bytes = Oracle_final FFI_failed.
Proof. reflexivity. Qed.
