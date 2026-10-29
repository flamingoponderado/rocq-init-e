(** A computable copy of Galette's Pancake evaluator [panSem.evaluate_c].

    [panSem] decides memory domains, shape equality and argument shapes
    classically, so it does not reduce under [vm_compute].  This copy decides
    them with the booleans [md]/[smd] and computable instances, and reads
    memory from a trie [t] kept beside the state.  It still writes the state's
    own [memory] field exactly as [panSem] does, so the states it returns are
    the ones [panSem] returns ([Evaluator]'s correctness theorem in
    [EvaluatorCorrect]). *)
From Stdlib Require Import FMapPositive.
From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
Import byte.ByteBits.
From Galette.HOL.src.n_bit.byte Require Import word_of_bytes4.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require wordLang backend_common.
From Galette.cakeml.pancake Require Import panLang.
From Galette.cakeml.pancake Require panStatic.
From Galette.cakeml.pancake.semantics Require Import panSem.
Open Scope N_scope.

(** Computable decisions for the propositions [panSem] decides classically. *)
#[global] Instance shape_eq_decision : EqDecision shape | 0 := panStatic.shape_eq_dec_f.

Definition none_decision {A} (x : option A) : Decision (x = None).
Proof. destruct x; [right; discriminate|left; reflexivity]. Defined.
#[global] Existing Instance none_decision | 0.

Fixpoint list_rel_decision {A B} (R : A -> B -> Prop) `{forall x y, Decision (R x y)}
    (l1 : list A) (l2 : list B) : Decision (LIST_REL R l1 l2).
Proof.
  destruct l1 as [|x l1], l2 as [|y l2].
  - left; constructor.
  - right; intros H0; inversion H0.
  - right; intros H0; inversion H0.
  - destruct (decide (R x y)) as [Hr|Hr].
    + destruct (list_rel_decision A B R _ l1 l2) as [Hl|Hl].
      * left; constructor; assumption.
      * right; intros H0; inversion H0; contradiction.
    + right; intros H0; inversion H0; contradiction.
Defined.
#[global] Existing Instance list_rel_decision | 0.

Lemma bool_decide_irrel (P : Prop) (d1 d2 : Decision P) :
  @bool_decide P d1 = @bool_decide P d2.
Proof. unfold bool_decide; destruct d1, d2; reflexivity || contradiction. Qed.

Module WordTrie.
Section WordTrie.
Context {a : N} {V : Type} (base : word a -> V).

Definition t := PositiveMap.t V.
Definition key (w : word a) : positive := N.succ_pos (w2n w).
Definition get (m : t) (w : word a) : V :=
  match PositiveMap.find (key w) m with Some v => v | None => base w end.
Definition set (w : word a) (v : V) (m : t) : t := PositiveMap.add (key w) v m.

Lemma key_inj w1 w2 : key w1 = key w2 -> w1 = w2.
Proof.
  unfold key; intros E; apply word_eq_w2n.
  apply (f_equal Pos.pred_N) in E; rewrite !N.pos_pred_succ in E; exact E.
Qed.

Lemma get_set m w v x : get (set w v m) x = (w =+ v) (get m) x.
Proof.
  unfold get, set; rewrite APPLY_UPDATE_THM.
  destruct (decide (w = x)) as [->|Hne].
  - rewrite PositiveMap.gss; reflexivity.
  - rewrite PositiveMap.gso; [reflexivity|].
    intros E; apply Hne, key_inj; symmetry; exact E.
Qed.
End WordTrie.
End WordTrie.

Section Evaluator.
Context {a : N} {ffi_t : Type}.
Variables (base : word a -> word_lab a) (md smd : word a -> bool).
Local Open Scope word_scope.

Abbreviation trie := (WordTrie.t (V := word_lab a)).
Abbreviation tget := (WordTrie.get base).
Abbreviation tset := WordTrie.set.

Definition c_mem_load_byte (t : trie) (be : bool) (w : word a) : option word8 :=
  match tget t (byte_align w) with
  | Word v => if md (byte_align w) then SOME (get_byte w v be) else NONE
  end.

Definition c_mem_load_32 (t : trie) (be : bool) (w : word a) : option word32 :=
  if aligned 2 w then
    match tget t (byte_align w) with
    | Word v =>
        if md (byte_align w)
        then SOME (word_of_bytes be (n2w 0 : word32)
                     [get_byte w v be; get_byte (w + n2w 1) v be;
                      get_byte (w + n2w 2) v be; get_byte (w + n2w 3) v be])
        else NONE
    end
  else NONE.

Fixpoint c_mem_load_f (fuel : nat) (stcs : list (stcname * struct_info))
    (sh : shape) (addr : word a) (t : trie) {struct fuel} : option (v a) :=
  let fix go (sh : shape) (addr : word a) {struct sh} : option (v a) :=
    match sh with
    | One => if md addr then SOME (Val (tget t addr)) else NONE
    | Comb shapes =>
        let fix loads (shapes : list shape) (addr : word a) : option (list (v a)) :=
          match shapes with
          | [] => SOME []
          | shape :: shapes =>
              match go shape addr,
                    loads shapes (addr + bytes_in_word * n2w (size_of_sh_with_ctxt stcs shape)) with
              | Some v, Some vs => SOME (v :: vs)
              | _, _ => NONE
              end
          end in
        match loads shapes addr with Some vs => SOME (RStruct vs) | None => NONE end
    | Named nm =>
        match dropWhile (fun '(n, i) => negb (bool_decide (n = nm))) stcs with
        | (nm, info) :: stcs' =>
            match fuel with
            | O => NONE
            | Datatypes.S fuel' =>
                let fix flds (fields : list (fldname * shape)) (addr : word a)
                    : option (list (fldname * v a)) :=
                  match fields with
                  | [] => SOME []
                  | (fld, shape) :: fields =>
                      match c_mem_load_f fuel' stcs' shape addr t,
                            flds fields (addr + bytes_in_word * n2w (size_of_sh_with_ctxt stcs' shape)) with
                      | Some v, Some vflds => SOME ((fld, v) :: vflds)
                      | _, _ => NONE
                      end
                  end in
                match flds (fields info) addr with
                | Some vflds => SOME (NStruct nm vflds)
                | None => NONE
                end
            end
        | _ => NONE
        end
    end in
  go sh addr.

Definition c_mem_load (sh : shape) (addr : word a) (t : trie)
    (stcs : list (stcname * struct_info)) : option (v a) :=
  c_mem_load_f (Datatypes.S (List.length stcs)) stcs sh addr t.

Fixpoint c_eval (s : state a ffi_t) (t : trie) (e : exp a) {struct e} : option (v a) :=
  match e with
  | Const w => SOME (ValWord w)
  | Var Local v => FLOOKUP (locals s) v
  | Var Global v => FLOOKUP (globals s) v
  | panLang.RStruct es =>
      match OPT_MMAP (c_eval s t) es with SOME vs => SOME (RStruct vs) | NONE => NONE end
  | RField index e =>
      match c_eval s t e with
      | SOME (RStruct vs) => if (index <? LENGTH vs)%N then SOME (EL index vs) else NONE
      | _ => NONE
      end
  | panLang.NStruct nm eflds =>
      let field_names := MAP fst eflds in
      match ALOOKUP (structs s) nm with
      | SOME info =>
          let '(field_names', field_shapes) := UNZIP (fields info) in
          if bool_decide (field_names' = field_names) then
            match OPT_MMAP (fun p => c_eval s t (snd p)) eflds with
            | SOME field_vals =>
                if EVERY (fun '(s, v) => bool_decide (s = shape_of v)) (ZIP (field_shapes, field_vals))
                then SOME (NStruct nm (ZIP (field_names, field_vals)))
                else NONE
            | NONE => NONE
            end
          else NONE
      | NONE => NONE
      end
  | NField fld e =>
      match c_eval s t e with
      | SOME (NStruct nm vflds) =>
          if negb (bool_decide (ALOOKUP (structs s) nm = NONE)) then ALOOKUP vflds fld else NONE
      | _ => NONE
      end
  | Load shape addr =>
      if is_wf_shape (structs s) shape then
        match c_eval s t addr with
        | SOME (Val (Word w)) => c_mem_load shape w t (structs s)
        | _ => NONE
        end
      else NONE
  | Load32 addr =>
      match c_eval s t addr with
      | SOME (Val (Word w)) =>
          match c_mem_load_32 t (be s) w with
          | NONE => NONE
          | SOME w => SOME (ValWord (w2w w))
          end
      | _ => NONE
      end
  | LoadByte addr =>
      match c_eval s t addr with
      | SOME (Val (Word w)) =>
          match c_mem_load_byte t (be s) w with
          | NONE => NONE
          | SOME w => SOME (ValWord (w2w w))
          end
      | _ => NONE
      end
  | Op op es =>
      match OPT_MMAP (c_eval s t) es with
      | SOME ws =>
          if EVERY (fun w => match w with Val (Word _) => true | _ => false end) ws
          then OPTION_MAP ValWord
                 (wordLang.word_op op (MAP (fun w => match w with Val (Word n) => n | _ => ARB end) ws))
          else NONE
      | _ => NONE
      end
  | Panop op es =>
      match OPT_MMAP (c_eval s t) es with
      | SOME ws =>
          if EVERY (fun w => match w with Val (Word _) => true | _ => false end) ws
          then OPTION_MAP ValWord
                 (pan_op op (MAP (fun w => match w with Val (Word n) => n | _ => ARB end) ws))
          else NONE
      | _ => NONE
      end
  | Cmp cmp e1 e2 =>
      match c_eval s t e1, c_eval s t e2 with
      | SOME (Val (Word w1)), SOME (Val (Word w2)) =>
          SOME (ValWord (if word_cmp cmp w1 w2 then n2w 1 else n2w 0))
      | _, _ => NONE
      end
  | Shift sh e1 e2 =>
      match c_eval s t e1, c_eval s t e2 with
      | SOME (Val (Word w1)), SOME (Val (Word w2)) =>
          OPTION_MAP ValWord (wordLang.word_sh sh w1 (w2n w2))
      | _, _ => NONE
      end
  | BaseAddr => SOME (ValWord (base_addr s))
  | TopAddr => SOME (ValWord (top_addr s))
  | BytesInWord => SOME (ValWord bytes_in_word)
  end.

(** Memories are pairs: [panSem]'s function, which is only written, and the
    trie that every read uses. *)
Definition cmem : Type := (word a -> word_lab a) * trie.

Definition c_mem_store_byte (m : cmem) (be : bool) (w : word a) (b : word8) : option cmem :=
  match tget (snd m) (byte_align w) with
  | Word v =>
      if md (byte_align w)
      then SOME ((byte_align w =+ Word (set_byte w b v be)) (fst m),
                 tset (byte_align w) (Word (set_byte w b v be)) (snd m))
      else NONE
  end.

Fixpoint c_write_bytearray (a0 : word a) (bs : list word8) (m : cmem) (be : bool) : cmem :=
  match bs with
  | [] => m
  | b :: bs =>
      match c_mem_store_byte (c_write_bytearray (a0 + n2w 1) bs m be) be a0 b with
      | SOME m => m
      | NONE => m
      end
  end.

Definition c_mem_store_32 (m : cmem) (be : bool) (w : word a) (hw : word32) : option cmem :=
  if aligned 2 w then
    match tget (snd m) (byte_align w) with
    | Word v =>
        if md (byte_align w) then
          let v0 := set_byte w (get_byte (n2w 0 : word32) hw be) v be in
          let v1 := set_byte (w + n2w 1) (get_byte (n2w 1) hw be) v0 be in
          let v2 := set_byte (w + n2w 2) (get_byte (n2w 2) hw be) v1 be in
          let v3 := set_byte (w + n2w 3) (get_byte (n2w 3) hw be) v2 be in
          SOME ((byte_align w =+ Word v3) (fst m), tset (byte_align w) (Word v3) (snd m))
        else NONE
    end
  else NONE.

Definition c_mem_store (addr : word a) (w : word_lab a) (m : cmem) : option cmem :=
  if md addr then SOME ((addr =+ w) (fst m), tset addr w (snd m)) else NONE.

Fixpoint c_mem_stores (a0 : word a) (ws : list (word_lab a)) (m : cmem) : option cmem :=
  match ws with
  | [] => SOME m
  | w :: ws =>
      match c_mem_store a0 w m with
      | SOME m' => c_mem_stores (a0 + bytes_in_word) ws m'
      | NONE => NONE
      end
  end.

Definition c_is_valid_value (s : state a ffi_t) (vk : varkind) (v0 : varname) (value : v a) : bool :=
  match lookup_kvar vk v0 s with
  | SOME w => bool_decide (shape_of value = shape_of w)
  | NONE => false
  end.

Definition c_lookup_code {K Nm P R} `{EqDecision Nm}
    (code0 : fmap K (list (Nm * shape) * (P * R)))
    (fname : K) (args : list (v a))
    : option (P * (fmap Nm (v a) * R)) :=
  match FLOOKUP code0 fname with
  | SOME (vshapes, (prog0, rshape)) =>
      if andb (ALL_DISTINCT (MAP fst vshapes))
              (bool_decide (LIST_REL (fun vshape arg => snd vshape = shape_of arg) vshapes args))
      then SOME (prog0, (FEMPTY |++ ZIP (MAP fst vshapes, args), rshape))
      else NONE
  | _ => NONE
  end.

Definition c_sh_mem_load (vk : varkind) (v0 : varname) (addr : word a) (nb : N) (s : state a ffi_t)
    : option (result a) * state a ffi_t :=
  if (nb =? 0)%N then
    (if smd addr then
       match call_FFI (ffi s) (SharedMem MappedRead) [n2w nb] (word_to_bytes addr false) with
       | FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s)
       | FFI_return new_ffi new_bytes =>
           (NONE, set_ffi new_ffi (set_kvar vk v0 (ValWord (word_of_bytes false (n2w 0) new_bytes)) s))
       end
     else (SOME Error, s))
  else
    (if smd (byte_align addr) then
       match call_FFI (ffi s) (SharedMem MappedRead) [n2w nb] (word_to_bytes addr false) with
       | FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s)
       | FFI_return new_ffi new_bytes =>
           (NONE, set_ffi new_ffi (set_kvar vk v0 (ValWord (word_of_bytes false (n2w 0) new_bytes)) s))
       end
     else (SOME Error, s)).

Definition c_sh_mem_store {b} (w : word b) (addr : word a) (nb : N) (s : state a ffi_t)
    : option (result a) * state a ffi_t :=
  if (nb =? 0)%N then
    (if smd addr then
       match call_FFI (ffi s) (SharedMem MappedWrite) [n2w nb]
               (word_to_bytes w false ++ word_to_bytes addr false) with
       | FFI_final outcome => (SOME (FinalFFI outcome), s)
       | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
       end
     else (SOME Error, s))
  else
    (if smd (byte_align addr) then
       match call_FFI (ffi s) (SharedMem MappedWrite) [n2w nb]
               (TAKE nb (word_to_bytes w false) ++ word_to_bytes addr false) with
       | FFI_final outcome => (SOME (FinalFFI outcome), s)
       | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
       end
     else (SOME Error, s)).

(** Results carry the trie beside [panSem]'s result and state. *)
Definition cres : Type := option (result a) * state a ffi_t * trie.

Definition c_fix_clock (old_s : state a ffi_t) (p : cres) : cres :=
  let '(r, t) := p in (fix_clock old_s r, t).

Definition c_with_memory (m : cmem) (s : state a ffi_t) : state a ffi_t * trie :=
  (set_memory (fst m) s, snd m).

Definition c_evaluate_body
    (go lower : prog a -> state a ffi_t -> trie -> cres)
    (p : prog a) (s : state a ffi_t) (t : trie) : cres :=
  match p with
  | Skip => (NONE, s, t)
  | Dec v0 sh e prog0 =>
      match c_eval s t e with
      | SOME value =>
          if bool_decide (sh = shape_of value) then
            let '(res, st, t') := go prog0 (set_locals (locals s |+ (v0, value)) s) t in
            (res, set_locals (res_var (locals st) (v0, FLOOKUP (locals s) v0)) st, t')
          else (SOME Error, s, t)
      | NONE => (SOME Error, s, t)
      end
  | Assign vk v0 src =>
      match c_eval s t src with
      | SOME value =>
          if c_is_valid_value s vk v0 value then (NONE, set_kvar vk v0 value s, t)
          else (SOME Error, s, t)
      | NONE => (SOME Error, s, t)
      end
  | Primitive v0 pop es =>
      match OPT_MMAP (c_eval s t) es with
      | SOME vs =>
          match pan_primop pop vs with
          | SOME value =>
              if c_is_valid_value s Local v0 value then (NONE, set_var v0 value s, t)
              else (SOME Error, s, t)
          | NONE => (SOME Error, s, t)
          end
      | _ => (SOME Error, s, t)
      end
  | Store dst src =>
      match c_eval s t dst, c_eval s t src with
      | SOME (Val (Word addr)), SOME value =>
          match c_mem_stores addr (flatten value) (memory s, t) with
          | SOME m => (NONE, set_memory (fst m) s, snd m)
          | NONE => (SOME Error, s, t)
          end
      | _, _ => (SOME Error, s, t)
      end
  | Store32 dst src =>
      match c_eval s t dst, c_eval s t src with
      | SOME (Val (Word adr)), SOME (Val (Word w)) =>
          match c_mem_store_32 (memory s, t) (be s) adr (w2w w) with
          | SOME m => (NONE, set_memory (fst m) s, snd m)
          | NONE => (SOME Error, s, t)
          end
      | _, _ => (SOME Error, s, t)
      end
  | StoreByte dst src =>
      match c_eval s t dst, c_eval s t src with
      | SOME (Val (Word adr)), SOME (Val (Word w)) =>
          match c_mem_store_byte (memory s, t) (be s) adr (w2w w) with
          | SOME m => (NONE, set_memory (fst m) s, snd m)
          | NONE => (SOME Error, s, t)
          end
      | _, _ => (SOME Error, s, t)
      end
  | ShMemLoad op vk v0 ad =>
      match c_eval s t ad with
      | SOME (Val (Word addr)) =>
          match lookup_kvar vk v0 s with
          | SOME (Val (Word _)) => (c_sh_mem_load vk v0 addr (nb_op op) s, t)
          | _ => (SOME Error, s, t)
          end
      | _ => (SOME Error, s, t)
      end
  | ShMemStore op ad e =>
      match c_eval s t ad, c_eval s t e with
      | SOME (Val (Word addr)), SOME (Val (Word bytes)) => (c_sh_mem_store bytes addr (nb_op op) s, t)
      | _, _ => (SOME Error, s, t)
      end
  | Seq c1 c2 =>
      let '(res, s1, t1) := c_fix_clock s (go c1 s t) in
      match res with NONE => go c2 s1 t1 | _ => (res, s1, t1) end
  | If e c1 c2 =>
      match c_eval s t e with
      | SOME (Val (Word w)) =>
          if negb (bool_decide (w = n2w 0)) then go c1 s t else go c2 s t
      | _ => (SOME Error, s, t)
      end
  | panLang.Break => (SOME Break, s, t)
  | panLang.Continue => (SOME Continue, s, t)
  | While e c =>
      match c_eval s t e with
      | SOME (Val (Word w)) =>
          if negb (bool_decide (w = n2w 0)) then
            if (clock s =? 0)%N then (SOME TimeOut, empty_locals s, t)
            else
              let '(res, s1, t1) := c_fix_clock (dec_clock s) (go c (dec_clock s) t) in
              match res with
              | SOME Continue => lower (While e c) s1 t1
              | NONE => lower (While e c) s1 t1
              | SOME Break => (NONE, s1, t1)
              | _ => (res, s1, t1)
              end
          else (NONE, s, t)
      | _ => (SOME Error, s, t)
      end
  | panLang.Return e =>
      match c_eval s t e with
      | SOME value =>
          if (size_of_sh_with_ctxt (structs s) (shape_of value) <=? 32)%N
          then (SOME (Return value), empty_locals s, t)
          else (SOME Error, s, t)
      | _ => (SOME Error, s, t)
      end
  | Raise eid e =>
      match FLOOKUP (eshapes s) eid, c_eval s t e with
      | SOME sh, SOME value =>
          if andb (bool_decide (shape_of value = sh))
                  (size_of_sh_with_ctxt (structs s) (shape_of value) <=? 32)%N
          then (SOME (Exception eid value), empty_locals s, t)
          else (SOME Error, s, t)
      | _, _ => (SOME Error, s, t)
      end
  | Tick =>
      if (clock s =? 0)%N then (SOME TimeOut, empty_locals s, t) else (NONE, dec_clock s, t)
  | Annot _ _ => (NONE, s, t)
  | Call caltyp fname argexps =>
      match OPT_MMAP (c_eval s t) argexps with
      | SOME args =>
          match c_lookup_code (code s) fname args with
          | SOME (prog0, (newlocals, return_sh)) =>
              if (clock s =? 0)%N then (SOME TimeOut, empty_locals s, t)
              else
                match c_fix_clock (set_locals newlocals (dec_clock s))
                        (lower prog0 (set_locals newlocals (dec_clock s)) t) with
                | (NONE, st, t') => (SOME Error, st, t')
                | (SOME Break, st, t') => (SOME Error, st, t')
                | (SOME Continue, st, t') => (SOME Error, st, t')
                | (SOME (Return retv), st, t') =>
                    if negb (bool_decide (shape_of retv = return_sh)) then (SOME Error, st, t')
                    else
                      match caltyp with
                      | NONE => (SOME (Return retv), empty_locals st, t')
                      | SOME (NONE, _) => (NONE, set_locals (locals s) st, t')
                      | SOME (SOME (rk, rt), _) =>
                          if c_is_valid_value s rk rt retv
                          then (NONE, set_kvar rk rt retv (set_locals (locals s) st), t')
                          else (SOME Error, st, t')
                      end
                | (SOME (Exception eid exn), st, t') =>
                    match caltyp with
                    | NONE => (SOME (Exception eid exn), empty_locals st, t')
                    | SOME (_, NONE) => (SOME (Exception eid exn), empty_locals st, t')
                    | SOME (_, SOME (eid', (evar, p))) =>
                        if bool_decide (eid = eid') then
                          match FLOOKUP (eshapes s) eid with
                          | SOME sh =>
                              if andb (bool_decide (shape_of exn = sh))
                                      (c_is_valid_value s Local evar exn)
                              then lower p (set_var evar exn (set_locals (locals s) st)) t'
                              else (SOME Error, st, t')
                          | NONE => (SOME Error, st, t')
                          end
                        else (SOME (Exception eid exn), empty_locals st, t')
                    end
                | (res, st, t') => (res, empty_locals st, t')
                end
          | _ => (SOME Error, s, t)
          end
      | _ => (SOME Error, s, t)
      end
  | DecCall rt shape fname argexps prog1 =>
      match OPT_MMAP (c_eval s t) argexps with
      | SOME args =>
          match c_lookup_code (code s) fname args with
          | SOME (prog0, (newlocals, return_sh)) =>
              if (clock s =? 0)%N then (SOME TimeOut, empty_locals s, t)
              else
                match c_fix_clock (set_locals newlocals (dec_clock s))
                        (lower prog0 (set_locals newlocals (dec_clock s)) t) with
                | (NONE, st, t') => (SOME Error, st, t')
                | (SOME Break, st, t') => (SOME Error, st, t')
                | (SOME Continue, st, t') => (SOME Error, st, t')
                | (SOME (Return retv), st, t') =>
                    if andb (bool_decide (shape_of retv = shape))
                            (bool_decide (shape_of retv = return_sh)) then
                      let '(res', st', t'') :=
                        lower prog1 (set_var rt retv (set_locals (locals s) st)) t' in
                      (res', set_locals (res_var (locals st') (rt, FLOOKUP (locals s) rt)) st', t'')
                    else (SOME Error, st, t')
                | (res, st, t') => (res, empty_locals st, t')
                end
          | _ => (SOME Error, s, t)
          end
      | _ => (SOME Error, s, t)
      end
  | ExtCall ffi_index ptr1 len1 ptr2 len2 =>
      match c_eval s t ptr1, c_eval s t len1, c_eval s t ptr2, c_eval s t len2 with
      | SOME (Val (Word sz1)), SOME (Val (Word ad1)), SOME (Val (Word sz2)), SOME (Val (Word ad2)) =>
          match read_bytearray sz1 (w2n ad1) (c_mem_load_byte t (be s)),
                read_bytearray sz2 (w2n ad2) (c_mem_load_byte t (be s)) with
          | SOME bytes, SOME bytes2 =>
              match call_FFI (ffi s) (ffi.ExtCall ffi_index) bytes bytes2 with
              | FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s, t)
              | FFI_return new_ffi new_bytes =>
                  let nmem := c_write_bytearray sz2 new_bytes (memory s, t) (be s) in
                  (NONE, set_ffi new_ffi (set_memory (fst nmem) s), snd nmem)
              end
          | _, _ => (SOME Error, s, t)
          end
      | _, _, _, _ => (SOME Error, s, t)
      end
  end.

Fixpoint c_evaluate_c (cf : nat) (p0 : prog a) (s0 : state a ffi_t) (t0 : trie) {struct cf} : cres :=
  let lower (p : prog a) (s : state a ffi_t) (t : trie) : cres :=
    match cf with O => (SOME Error, s, t) | Datatypes.S cf' => c_evaluate_c cf' p s t end in
  let fix go (p : prog a) (s : state a ffi_t) (t : trie) {struct p} : cres :=
    c_evaluate_body go lower p s t in
  go p0 s0 t0.

(** [panSem.evaluate_decls]; global initializers are evaluated with [c_eval]. *)
Fixpoint c_evaluate_decls (s : state a ffi_t) (t : trie) (ds : list (decl a)) : option (state a ffi_t) :=
  match ds with
  | [] => SOME s
  | Name nm flds :: ds => c_evaluate_decls s t ds
  | Decl sh v0 e :: ds =>
      match c_eval (set_locals FEMPTY s) t e with
      | SOME res =>
          if bool_decide (sh = shape_of res)
          then c_evaluate_decls (set_globals (globals s |+ (v0, res)) s) t ds
          else NONE
      | NONE => NONE
      end
  | Function fi :: ds =>
      if andb (EVERY (is_wf_shape (structs s) ∘ snd) (params fi))
              (is_wf_shape (structs s) (fun_decl_return fi))
      then c_evaluate_decls
             (set_code (code s |+ (name fi, (params fi, (body fi, fun_decl_return fi)))) s) t ds
      else NONE
  | ExnDecl eid sh :: ds =>
      if andb (bool_decide (FLOOKUP (eshapes s) eid = NONE)) (is_wf_shape (structs s) sh)
      then c_evaluate_decls (set_eshapes (eshapes s |+ (eid, sh)) s) t ds
      else NONE
  end.

End Evaluator.
