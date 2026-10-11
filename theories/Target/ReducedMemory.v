(** Original physical memory branch: MMU/Access, Translate and Primitives.
    Unaligned accesses and arbitrary byte counts retain the literal behavior. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.Target Require Import ReducedTypes ReducedStateOps ReducedUpperJump.
Open Scope N_scope.
Definition translateAddr (arg : word 64*(fetchType*accessType)) (s : riscv_state)
 : option (word 64)*riscv_state := (Some (fst arg),s).
Definition vmType (_ : word 5) (s : riscv_state) : VM_Mode*riscv_state := (Mbare,s).
Definition MEM (index : word 61) (s : riscv_state) : word 64 :=
 let b := word_lsl (w2w index : word 64) 3 in
 let byte := fun i => riscv_state_MEM8 s (word_add b (n2w i)) in
 word_concat (byte 7) (word_concat (byte 6) (word_concat (byte 5)
 (word_concat (byte 4) (word_concat (byte 3) (word_concat (byte 2)
 (word_concat (byte 1) (byte 0) : word 16) : word 24) : word 32) : word 40) : word 48) : word 56).
Definition writeMEM (value : word 64) (index : word 61) (s : riscv_state) : riscv_state :=
 let b := word_lsl (w2w index : word 64) 3 in
 let put := fun (i : N) (t : riscv_state) => riscv_state_MEM8_fupd
  (fun old => update (word_add b (n2w i)) (w2w (word_lsr value (8*i)) : word 8) old) t in
 put 0 (put 1 (put 2 (put 3 (put 4 (put 5 (put 6 (put 7 s))))))).
Definition rawReadData (address : word 64) (s : riscv_state) : word 64 :=
 let index := (w2w (word_lsr address 3) : word 61) in
 let align := w2n (w2w address : word 3) in
 if align =? 0 then MEM index s else
 w2w (word_asr (word_concat (MEM (word_add index (n2w 1)) s) (MEM index s) : word 128) (align*8)).
Definition rawWriteData (address data : word 64) (nbytes : N) (s : riscv_state) : riscv_state :=
 let mask := word_sub (word_lsl (n2w 1 : word 64) (nbytes*8)) (n2w 1) in
 let index := (w2w (word_lsr address 3) : word 61) in
 let align := w2n (w2w address : word 3) in
 let old := MEM index s in
 if align =? 0 then writeMEM (word_or (word_and old (word_1comp mask)) (word_and data mask)) index s
 else if align+nbytes <=? 8 then
 writeMEM (word_or (word_and old (word_1comp (word_lsl mask (align*8))))
  (word_lsl (word_and data mask) (align*8))) index s else
 let dw_mask := word_lsl (w2w mask : word 128) (align*8) in
 let dw_old := (word_concat (MEM (word_add index (n2w 1)) s) old : word 128) in
 let dw_new := word_or (word_and dw_old (word_1comp dw_mask))
  (word_and (word_lsl (w2w data : word 128) (align*8)) dw_mask) in
 writeMEM (w2w dw_new) index (writeMEM (w2w (word_lsr dw_new 64)) (word_add index (n2w 1)) s).
Definition writeSkip (value : word 64) (s : riscv_state) : riscv_state :=
 riscv_state_c_Skip_fupd (fun old => update (riscv_state_procID s) value old) s.
Definition rawReadInst (address : word 64) (s : riscv_state) : rawInstType*riscv_state :=
 let first := riscv_state_MEM8 s address in
 if fcp_index first 1 && fcp_index first 0 then
 let t := writeSkip (n2w 4) s in
 let byte := fun i => riscv_state_MEM8 t (word_add address (n2w i)) in
 (Word (word_concat (byte 3) (word_concat (byte 2) (word_concat (byte 1) (byte 0) : word 16) : word 24)),t)
 else let t := writeSkip (n2w 2) s in
 (Half (word_concat (riscv_state_MEM8 t (word_add address (n2w 1))) (riscv_state_MEM8 t address)),t).
Definition Fetch (s : riscv_state) : rawInstType*riscv_state :=
 let '(address,t) := translateAddr (PC s,(Instruction,Read)) s in
 match address with Some a => rawReadInst a t | None => rawReadInst ARB t end.
