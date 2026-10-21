(** Guest input framing and shared-memory handlers. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.cakeml.semantics.ffi Require Import ffi.
From InitE.Guest Require Import GasLimit ByteCodec.
From InitE.InitE Require Import Parameters.
Open Scope N_scope.
Definition HostMemory := word 64 -> option word8.
Definition hostInputBytes (input : InputBlob) : list word8 :=
 REPLICATE 8 (n2w 0) ++ leBytes (n2w (LENGTH input)) ++ input ++
 REPLICATE ((8 - LENGTH input mod 8) mod 8) (n2w 0).
Definition guestHostMemory (input : InputBlob) : HostMemory :=
 let bytes := hostInputBytes input in
 fun address =>
 if (inputStart <=? w2n address) && (w2n address <? inputEnd)
 then Some (nthN (w2n address-inputStart) bytes (n2w 0))
 else if (outputStart <=? w2n address) && (w2n address <? outputEnd)
 then Some (n2w 0) else None.
Definition sharedWidth (configuration : list word8) : N :=
 match configuration with
 | [width] => if w2n width =? 0 then 8 else w2n width
 | _ => 0
 end.
Fixpoint readHost (host : HostMemory) (addresses : list (word 64)) : option (list word8) :=
 match addresses with
 | [] => Some []
 | a::rest => match host a, readHost host rest with
              | Some b, Some bs => Some (b::bs) | _,_ => None end
 end.
Definition sharedOracle (op : shmem_op) : oracle_function HostMemory :=
 fun host configuration bytes =>
 match op with
 | MappedRead =>
   let width := sharedWidth configuration in
   let address := wordOfLeBytes bytes in
   match readHost host (MAP (fun i => (address+n2w i)%w) (COUNT_LIST width)) with
   | Some values => Oracle_return host (values ++ REPLICATE (LENGTH bytes-width) (n2w 0))
   | None => Oracle_final FFI_failed
   end
 | MappedWrite =>
   let count := LENGTH bytes-8 in
   let values := TAKE count bytes in
   let address := wordOfLeBytes (DROP count bytes) in
   if EVERY (fun i => match host (address+n2w i)%w with Some _ => true | None => false end) (COUNT_LIST count)
   then Oracle_return (fun current =>
     let offset := w2n (current-address)%w in
     if (w2n address <=? w2n current) && (offset <? count)
     then nth_error values (N.to_nat offset) else host current) bytes
   else Oracle_final FFI_failed
 end.
Example input_length_frame :
 w2n (wordOfLeBytes (TAKE 8 (DROP 8 (hostInputBytes [n2w 17;n2w 18])))) = 2.
Proof. vm_compute; reflexivity. Qed.
Example arena_end_unmapped : guestHostMemory [] (n2w inputEnd) = None.
Proof. vm_compute; reflexivity. Qed.
Example output_zero : guestHostMemory [] (n2w outputStart) = Some (n2w 0).
Proof. vm_compute; reflexivity. Qed.
Example outside_read_fails :
 sharedOracle MappedRead (guestHostMemory []) [n2w 0] (leBytes (n2w inputEnd)) = Oracle_final FFI_failed.
Proof. vm_compute; reflexivity. Qed.
