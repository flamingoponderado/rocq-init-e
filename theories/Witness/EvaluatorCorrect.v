(** [Witness.Evaluator] computes [panSem]'s results.

    For states whose memory domains are decided by [md]/[smd] and whose
    memory agrees with the trie, [c_evaluate_c] returns exactly
    [panSem.evaluate_c]'s result and state, together with a trie that again
    agrees with the returned memory. *)
From Stdlib Require Import FMapPositive.
From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.pancake Require Import panLang.
From Galette.cakeml.pancake.semantics Require Import panSem.
From InitE.Witness Require Import Evaluator.
Open Scope N_scope.

Fixpoint exp_nested_ind {a} (P : exp a -> Prop)
    (Hconst : forall w, P (Const w)) (Hvar : forall k v, P (Var k v))
    (Hrs : forall es, Forall P es -> P (panLang.RStruct es))
    (Hrf : forall i e, P e -> P (RField i e))
    (Hns : forall nm fl, Forall (fun p => P (snd p)) fl -> P (panLang.NStruct nm fl))
    (Hnf : forall f e, P e -> P (NField f e))
    (Hld : forall sh e, P e -> P (Load sh e))
    (Hl32 : forall e, P e -> P (Load32 e))
    (Hlb : forall e, P e -> P (LoadByte e))
    (Hop : forall op es, Forall P es -> P (Op op es))
    (Hpop : forall op es, Forall P es -> P (Panop op es))
    (Hcmp : forall c e1 e2, P e1 -> P e2 -> P (Cmp c e1 e2))
    (Hsh : forall s e1 e2, P e1 -> P e2 -> P (Shift s e1 e2))
    (Hb : P BaseAddr) (Ht : P TopAddr) (Hbw : P BytesInWord) (e : exp a) {struct e} : P e :=
  let rec := exp_nested_ind P Hconst Hvar Hrs Hrf Hns Hnf Hld Hl32 Hlb Hop Hpop Hcmp Hsh Hb Ht Hbw in
  let fix all (l : list (exp a)) : Forall P l :=
    match l with [] => Forall_nil _ | x :: xs => Forall_cons _ (rec x) (all xs) end in
  match e with
  | Const w => Hconst w
  | Var k v => Hvar k v
  | panLang.RStruct es => Hrs es (all es)
  | RField i e => Hrf i e (rec e)
  | panLang.NStruct nm fl =>
      Hns nm fl ((fix flds (l : list (fldname * exp a)) : Forall (fun p => P (snd p)) l :=
                    match l with
                    | [] => Forall_nil _
                    | x :: xs => Forall_cons _ (rec (snd x)) (flds xs)
                    end) fl)
  | NField f e => Hnf f e (rec e)
  | Load sh e => Hld sh e (rec e)
  | Load32 e => Hl32 e (rec e)
  | LoadByte e => Hlb e (rec e)
  | Op op es => Hop op es (all es)
  | Panop op es => Hpop op es (all es)
  | Cmp c e1 e2 => Hcmp c e1 e2 (rec e1) (rec e2)
  | Shift s e1 e2 => Hsh s e1 e2 (rec e1) (rec e2)
  | BaseAddr => Hb
  | TopAddr => Ht
  | BytesInWord => Hbw
  end.

Lemma OPT_MMAP_ext {A B} (f g : A -> option B) l :
  Forall (fun x => f x = g x) l -> OPT_MMAP f l = OPT_MMAP g l.
Proof. induction 1 as [|x l Hx _ IH]; cbn; [reflexivity|]. rewrite Hx, IH; reflexivity. Qed.

Lemma EVERY_ext {A} (f g : A -> bool) l : (forall x, f x = g x) -> EVERY f l = EVERY g l.
Proof. intros H; induction l as [|x l IH]; cbn; [reflexivity|]. rewrite H, IH; reflexivity. Qed.

(** Rewrite every computable decision into [panSem]'s classical one. *)
Ltac classical_decisions :=
  repeat match goal with
  | |- context [@bool_decide ?P ?d] =>
      lazymatch d with
      | Classical.classical_decision _ => fail
      | _ => rewrite (bool_decide_irrel P d (Classical.classical_decision P))
      end
  end.

Lemma c_is_valid_value_eq {a ffi_t} :
  @c_is_valid_value a ffi_t = @is_valid_value a ffi_t.
Proof.
  do 4 (apply functional_extensionality; intro).
  unfold c_is_valid_value, is_valid_value; destruct (lookup_kvar _ _ _); [|reflexivity].
  classical_decisions; reflexivity.
Qed.

Lemma c_lookup_code_eq {a K Nm P R} `{EqDecision Nm} :
  @c_lookup_code a K Nm P R _ = @lookup_code a K Nm P R _.
Proof.
  do 3 (apply functional_extensionality; intro).
  unfold c_lookup_code, lookup_code; destruct (FLOOKUP _ _) as [[? [? ?]]|]; [|reflexivity].
  classical_decisions; reflexivity.
Qed.

Section Correct.
Context {a : N} {ffi_t : Type}.
Variables (base : word a -> word_lab a) (md smd : word a -> bool) (D SD : word a -> Prop).
Hypothesis md_spec : forall w, md w = true <-> D w.
Hypothesis smd_spec : forall w, smd w = true <-> SD w.
Local Open Scope word_scope.

Abbreviation tget := (WordTrie.get base).

Definition Good (m : word a -> word_lab a) (t : WordTrie.t) : Prop := forall x, m x = tget t x.

Definition Rel (s : state a ffi_t) (t : WordTrie.t) : Prop :=
  memaddrs s = D /\ sh_memaddrs s = SD /\ Good (memory s) t.

Definition CR (c : cres) (x : option (result a) * state a ffi_t) : Prop :=
  fst c = x /\ Rel (snd (fst c)) (snd c).

Lemma decide_md {B} w (x y : B) : (if classical_dec (w IN D) then x else y) = (if md w then x else y).
Proof.
  unfold pred_set.IN; destruct (classical_dec (D w)) as [H|H]; destruct (md w) eqn:E; try reflexivity.
  - apply md_spec in H; congruence.
  - exfalso; apply H, md_spec, E.
Qed.

Lemma decide_smd {B} w (x y : B) : (if classical_dec (w IN SD) then x else y) = (if smd w then x else y).
Proof.
  unfold pred_set.IN; destruct (classical_dec (SD w)) as [H|H]; destruct (smd w) eqn:E; try reflexivity.
  - apply smd_spec in H; congruence.
  - exfalso; apply H, smd_spec, E.
Qed.

(** *** Loads *)

Lemma load_byte_eq m t be : Good m t -> c_mem_load_byte base md t be = mem_load_byte m D be.
Proof.
  intros G; apply functional_extensionality; intros w.
  unfold c_mem_load_byte, mem_load_byte; rewrite G; destruct (tget t _).
  rewrite decide_md; reflexivity.
Qed.

Lemma load_32_eq m t be w : Good m t -> c_mem_load_32 base md t be w = mem_load_32 m D be w.
Proof.
  intros G; unfold c_mem_load_32, mem_load_32; destruct (aligned 2 w); [|reflexivity].
  rewrite G; destruct (tget t _); rewrite decide_md; reflexivity.
Qed.

Definition c_mem_loads_f fuel stcs t :=
  fix loads (shapes : list shape) (addr : word a) : option (list (v a)) :=
    match shapes with
    | [] => SOME []
    | shape :: shapes =>
        match c_mem_load_f base md fuel stcs shape addr t,
              loads shapes (addr + bytes_in_word * n2w (size_of_sh_with_ctxt stcs shape)) with
        | Some v, Some vs => SOME (v :: vs)
        | _, _ => NONE
        end
    end.

Definition c_mem_load_flds_f fuel stcs t :=
  fix flds (fields : list (fldname * shape)) (addr : word a) : option (list (fldname * v a)) :=
    match fields with
    | [] => SOME []
    | (fld, shape) :: fields =>
        match c_mem_load_f base md fuel stcs shape addr t,
              flds fields (addr + bytes_in_word * n2w (size_of_sh_with_ctxt stcs shape)) with
        | Some v, Some vflds => SOME ((fld, v) :: vflds)
        | _, _ => NONE
        end
    end.

Lemma c_mem_load_f_Comb f stcs l addr t :
  c_mem_load_f base md (Datatypes.S f) stcs (Comb l) addr t =
  match c_mem_loads_f (Datatypes.S f) stcs t l addr with
  | Some vs => SOME (RStruct vs) | None => NONE end.
Proof.
  cbn [c_mem_load_f].
  match goal with |- match ?F l addr with _ => _ end = _ =>
    assert (E : forall l0 addr0, F l0 addr0 = c_mem_loads_f (Datatypes.S f) stcs t l0 addr0)
  end.
  { intros l0; induction l0 as [|x xs IH]; intros addr0; [reflexivity|].
    cbn [c_mem_loads_f]; try rewrite <- IH; reflexivity. }
  rewrite E; reflexivity.
Qed.

Lemma c_mem_load_f_Named f stcs nm addr t :
  c_mem_load_f base md f stcs (Named nm) addr t =
  match dropWhile (fun '(n, i) => negb (bool_decide (n = nm))) stcs with
  | (nm, info) :: stcs' =>
      match f with
      | O => NONE
      | Datatypes.S f' =>
          match c_mem_load_flds_f f' stcs' t (fields info) addr with
          | Some vflds => SOME (NStruct nm vflds) | None => NONE
          end
      end
  | _ => NONE
  end.
Proof.
  destruct f as [|f]; cbn [c_mem_load_f];
    destruct (dropWhile _ stcs) as [|[nm' info] stcs']; reflexivity.
Qed.

Lemma c_mem_load_f_eq m t : Good m t -> forall f stcs sh addr,
  (List.length stcs < f)%nat ->
  c_mem_load_f base md f stcs sh addr t = mem_load_f f stcs sh addr D m.
Proof.
  intros G f; induction f as [|f IH]; intros stcs sh addr Hf; [lia|].
  revert addr; induction sh as [| l Hl | nm] using shape_nested_ind; intros addr.
  - cbn; rewrite G, decide_md; reflexivity.
  - rewrite c_mem_load_f_Comb, mem_load_f_Comb.
    enough (E : forall addr0, c_mem_loads_f (Datatypes.S f) stcs t l addr0 =
                              mem_loads_f (Datatypes.S f) stcs l addr0 D m)
      by (rewrite E; reflexivity).
    induction Hl as [|x xs Hx Hxs IHl]; intros addr0; [reflexivity|].
    cbn [c_mem_loads_f mem_loads_f]. rewrite Hx, IHl. reflexivity.
  - rewrite c_mem_load_f_Named, mem_load_f_Named.
    pose proof (length_dropWhile (fun '(n, i) => negb (bool_decide (n = nm))) stcs) as Hd.
    destruct (dropWhile _ stcs) as [|[nm' info] stcs'] eqn:E; [reflexivity|].
    cbn [List.length] in Hd.
    enough (Efl : forall fl addr0, c_mem_load_flds_f f stcs' t fl addr0 =
                                   mem_load_flds_f f stcs' fl addr0 D m)
      by (rewrite Efl; reflexivity).
    intros fl; induction fl as [|[fld sh] fl IHf]; intros addr0; [reflexivity|].
    cbn [c_mem_load_flds_f mem_load_flds_f]. rewrite (IH stcs') by lia. rewrite IHf. reflexivity.
Qed.

Lemma c_eval_eq s t : Rel s t -> c_eval base md s t = eval s.
Proof.
  intros (HD & _ & G); apply functional_extensionality; intros e.
  induction e using exp_nested_ind; cbn [c_eval eval];
    repeat match goal with H : Forall _ _ |- _ => rewrite (OPT_MMAP_ext _ _ _ H); clear H end;
    repeat match goal with H : c_eval _ _ _ _ ?e = eval _ ?e |- _ => rewrite H; clear H end;
    try reflexivity.
  - destruct (ALOOKUP _ nm) as [info|]; [|reflexivity].
    destruct (UNZIP (fields info)) as [names shapes].
    destruct (bool_decide _); [|reflexivity].
    destruct (OPT_MMAP _ _) as [vals|]; [|reflexivity].
    rewrite (EVERY_ext _ (fun '(s, v) => @bool_decide _ (Classical.classical_decision (s = shape_of v))));
      [reflexivity|].
    intros [? ?]; apply bool_decide_irrel.
  - destruct (eval s e) as [[[?]| |]|]; try reflexivity. classical_decisions; reflexivity.
  - destruct (is_wf_shape _ _); [|reflexivity].
    destruct (eval s e) as [[[w]| |]|]; try reflexivity.
    unfold c_mem_load, mem_load; rewrite HD; apply c_mem_load_f_eq; [exact G|lia].
  - destruct (eval s e) as [[[w]| |]|]; try reflexivity. rewrite HD, (load_32_eq (memory s) t _ _ G); reflexivity.
  - destruct (eval s e) as [[[w]| |]|]; try reflexivity. rewrite HD, (load_byte_eq _ _ _ G); reflexivity.
Qed.

(** *** Stores *)

Lemma Good_update m t w x : Good m t -> Good ((w =+ x) m) (WordTrie.set w x t).
Proof. intros G y; rewrite WordTrie.get_set, !APPLY_UPDATE_THM, G; reflexivity. Qed.

Lemma cset_rel m t m' w x : Good m t ->
  SOME ((w =+ x) m) = SOME (fst (cset base w x (m', t))) /\
  Good (fst (cset base w x (m', t))) (snd (cset base w x (m', t))).
Proof.
  intros G; unfold cset; cbn [fst snd]; split; [|intros y; reflexivity].
  f_equal; apply functional_extensionality; intros y.
  rewrite WordTrie.get_set, !APPLY_UPDATE_THM, G; reflexivity.
Qed.

Definition StoreRel (c : option cmem) (o : option (word a -> word_lab a)) : Prop :=
  match c with
  | SOME cm => o = SOME (fst cm) /\ Good (fst cm) (snd cm)
  | NONE => o = NONE
  end.

Lemma store_byte_rel m t be w b : Good m t ->
  StoreRel (c_mem_store_byte base md (m, t) be w b) (mem_store_byte m D be w b).
Proof.
  intros G; unfold c_mem_store_byte, mem_store_byte, StoreRel; cbn [fst snd].
  rewrite G; destruct (tget t _); rewrite decide_md; destruct (md _); [|reflexivity].
  apply cset_rel, G.
Qed.

Lemma write_bytearray_rel m t a0 bs be : Good m t ->
  fst (c_write_bytearray base md a0 bs (m, t) be) = write_bytearray a0 bs m D be /\
  Good (fst (c_write_bytearray base md a0 bs (m, t) be)) (snd (c_write_bytearray base md a0 bs (m, t) be)).
Proof.
  intros G; revert a0; induction bs as [|b bs IH]; intros a0; [split; [reflexivity|exact G]|].
  cbn [c_write_bytearray write_bytearray].
  destruct (IH (a0 + n2w 1)) as [E G1].
  destruct (c_write_bytearray base md (a0 + n2w 1) bs (m, t) be) as [m1 t1]; cbn [fst snd] in E, G1.
  rewrite <- E. pose proof (store_byte_rel m1 t1 be a0 b G1) as H.
  destruct (c_mem_store_byte _ _ _ _ _ _) as [[m2 t2]|]; cbn in H |- *.
  - destruct H as [-> G2]; split; [reflexivity|exact G2].
  - rewrite H; split; [reflexivity|exact G].
Qed.

Lemma store_32_rel m t be w hw : Good m t ->
  StoreRel (c_mem_store_32 base md (m, t) be w hw) (mem_store_32 m D be w hw).
Proof.
  intros G; unfold c_mem_store_32, mem_store_32, StoreRel; cbn [fst snd].
  destruct (aligned 2 w); [|reflexivity].
  rewrite G; destruct (tget t _); rewrite decide_md; destruct (md _); [|reflexivity].
  apply cset_rel, G.
Qed.

Lemma stores_rel ws : forall m t a0, Good m t ->
  StoreRel (c_mem_stores base md a0 ws (m, t)) (mem_stores a0 ws D m).
Proof.
  induction ws as [|w ws IH]; intros m t a0 G; [split; [reflexivity|exact G]|].
  cbn [c_mem_stores mem_stores]; unfold c_mem_store, mem_store; cbn [fst snd].
  rewrite decide_md; destruct (md a0); [|reflexivity].
  destruct (cset_rel m t m a0 w G) as [E G']; injection E as ->.
  unfold cset in G' |- *; cbn [fst snd] in G' |- *. apply IH, G'.
Qed.

(** *** Shared memory *)

Lemma sh_mem_load_eq vk v0 addr nb (s : state a ffi_t) : sh_memaddrs s = SD ->
  c_sh_mem_load smd vk v0 addr nb s = sh_mem_load vk v0 addr nb s.
Proof. intros HS; unfold c_sh_mem_load, sh_mem_load; rewrite HS, !decide_smd; reflexivity. Qed.

Lemma sh_mem_store_eq {b} (w : word b) addr nb (s : state a ffi_t) : sh_memaddrs s = SD ->
  c_sh_mem_store smd w addr nb s = sh_mem_store w addr nb s.
Proof. intros HS; unfold c_sh_mem_store, sh_mem_store; rewrite HS, !decide_smd; reflexivity. Qed.

(** *** States *)

Lemma Rel_same s s' t : Rel s t -> memaddrs s' = memaddrs s -> sh_memaddrs s' = sh_memaddrs s ->
  memory s' = memory s -> Rel s' t.
Proof. intros (H1 & H2 & H3) E1 E2 E3; unfold Rel; rewrite E1, E2, E3; auto. Qed.

Lemma Rel_set_locals x s t : Rel s t -> Rel (set_locals x s) t.
Proof. intros H; apply (Rel_same _ _ _ H); reflexivity. Qed.
Lemma Rel_set_globals x s t : Rel s t -> Rel (set_globals x s) t.
Proof. intros H; apply (Rel_same _ _ _ H); reflexivity. Qed.
Lemma Rel_set_code x s t : Rel s t -> Rel (set_code x s) t.
Proof. intros H; apply (Rel_same _ _ _ H); reflexivity. Qed.
Lemma Rel_set_eshapes x s t : Rel s t -> Rel (set_eshapes x s) t.
Proof. intros H; apply (Rel_same _ _ _ H); reflexivity. Qed.
Lemma Rel_set_clock x s t : Rel s t -> Rel (set_clock x s) t.
Proof. intros H; apply (Rel_same _ _ _ H); reflexivity. Qed.
Lemma Rel_set_ffi x s t : Rel s t -> Rel (set_ffi x s) t.
Proof. intros H; apply (Rel_same _ _ _ H); reflexivity. Qed.
Lemma Rel_dec_clock s t : Rel s t -> Rel (dec_clock s) t.
Proof. intros H; apply (Rel_same _ _ _ H); reflexivity. Qed.
Lemma Rel_empty_locals s t : Rel s t -> Rel (empty_locals s) t.
Proof. intros H; apply (Rel_same _ _ _ H); reflexivity. Qed.
Lemma Rel_set_var v0 x s t : Rel s t -> Rel (set_var v0 x s) t.
Proof. intros H; apply (Rel_same _ _ _ H); reflexivity. Qed.
Lemma Rel_set_kvar vk v0 x s t : Rel s t -> Rel (set_kvar vk v0 x s) t.
Proof. intros H; apply (Rel_same _ _ _ H); destruct vk; reflexivity. Qed.
Lemma Rel_set_memory m s t t' : Rel s t -> Good m t' -> Rel (set_memory m s) t'.
Proof. intros (H1 & H2 & _) G; repeat split; assumption. Qed.

Lemma Rel_sh_mem_load vk v0 addr nb s t : Rel s t -> Rel (snd (sh_mem_load vk v0 addr nb s)) t.
Proof.
  intros H; unfold sh_mem_load.
  repeat (destruct (classical_dec _) || destruct (_ =? _) || destruct (call_FFI _ _ _ _)); cbn [snd];
    eauto using Rel_set_ffi, Rel_set_kvar, Rel_empty_locals.
Qed.

Lemma Rel_sh_mem_store {b} (w : word b) addr nb s t : Rel s t -> Rel (snd (sh_mem_store w addr nb s)) t.
Proof.
  intros H; unfold sh_mem_store.
  repeat (destruct (classical_dec _) || destruct (_ =? _) || destruct (call_FFI _ _ _ _)); cbn [snd];
    eauto using Rel_set_ffi.
Qed.

Ltac rel_tac :=
  solve [eauto 20 using Rel_set_locals, Rel_set_globals, Rel_set_clock, Rel_set_ffi, Rel_dec_clock,
           Rel_empty_locals, Rel_set_var, Rel_set_kvar, Rel_set_memory].

(** *** Programs *)

Definition c_lowerF (cf : nat) (p : prog a) (s : state a ffi_t) (t : WordTrie.t) : cres :=
  match cf with O => (SOME Error, s, t) | Datatypes.S cf' => c_evaluate_c base md smd cf' p s t end.

Lemma c_evaluate_c_unfold cf p s t :
  c_evaluate_c base md smd cf p s t =
  c_evaluate_body base md smd (c_evaluate_c base md smd cf) (c_lowerF cf) p s t.
Proof. destruct cf, p; reflexivity. Qed.

Definition Sound (cf : nat) (p : prog a) : Prop :=
  forall s t, Rel s t -> CR (c_evaluate_c base md smd cf p s t) (evaluate_c cf p s).

Definition LowerSound (cf : nat) : Prop :=
  forall p s t, Rel s t -> CR (c_lowerF cf p s t) (lowerF cf p s).

(** Replace a recursive result by its [panSem] counterpart. *)
Ltac use_cr H :=
  match type of H with CR ?c ?x =>
    revert H; generalize c; generalize x;
    let x0 := fresh "x" in let c0 := fresh "c" in let Hc := fresh "Hc" in
    intros x0 c0 Hc; destruct c0 as [[?r ?st] ?tt]; destruct Hc as [?Hx ?HR];
    cbn [fst snd] in *; subst x0
  end.

Ltac sub_cr :=
  match goal with
  | |- context [c_evaluate_c _ _ _ ?cf ?p ?s0 ?t0] =>
      match goal with H : Sound cf p |- _ =>
        let Hc := fresh "Hc" in pose proof (H s0 t0 ltac:(rel_tac)) as Hc; use_cr Hc end
  | |- context [c_lowerF ?cf ?p ?s0 ?t0] =>
      match goal with H : LowerSound cf |- _ =>
        let Hc := fresh "Hc" in pose proof (H p s0 t0 ltac:(rel_tac)) as Hc; use_cr Hc end
  end.

Ltac finish := split; [reflexivity|cbn [fst snd]; rel_tac].

Ltac mem_tac :=
  match goal with
  | G : Good (memory ?s0) ?t0 |- context [c_mem_stores _ _ ?a0 ?ws (memory ?s0, ?t0)] =>
      let H := fresh "H" in pose proof (stores_rel ws _ _ a0 G) as H; revert H;
      destruct (c_mem_stores _ _ a0 ws (memory s0, t0)) as [[?m ?tm]|]; cbn [StoreRel fst snd];
      [intros [-> ?G]|intros ->]
  | G : Good (memory ?s0) ?t0 |- context [c_mem_store_32 _ _ (memory ?s0, ?t0) ?be ?w ?hw] =>
      let H := fresh "H" in pose proof (store_32_rel _ _ be w hw G) as H; revert H;
      destruct (c_mem_store_32 _ _ (memory s0, t0) be w hw) as [[?m ?tm]|]; cbn [StoreRel fst snd];
      [intros [-> ?G]|intros ->]
  | G : Good (memory ?s0) ?t0 |- context [c_mem_store_byte _ _ (memory ?s0, ?t0) ?be ?w ?b] =>
      let H := fresh "H" in pose proof (store_byte_rel _ _ be w b G) as H; revert H;
      destruct (c_mem_store_byte _ _ (memory s0, t0) be w b) as [[?m ?tm]|]; cbn [StoreRel fst snd];
      [intros [-> ?G]|intros ->]
  | G : Good (memory ?s0) ?t0 |- context [c_write_bytearray _ _ ?a0 ?bs (memory ?s0, ?t0) ?be] =>
      let H := fresh "H" in pose proof (write_bytearray_rel _ _ a0 bs be G) as H; revert H;
      destruct (c_write_bytearray _ _ a0 bs (memory s0, t0) be) as [?m ?tm]; cbn [fst snd];
      intros [<- ?G]
  end.

Ltac sh_tac :=
  match goal with
  | HS : sh_memaddrs ?s0 = SD, HR : Rel ?s0 ?t0 |- CR (c_sh_mem_load _ ?vk ?v0 ?ad ?nb ?s0, ?t0) _ =>
      rewrite (sh_mem_load_eq vk v0 ad nb s0 HS); split; [reflexivity|apply Rel_sh_mem_load, HR]
  | HS : sh_memaddrs ?s0 = SD, HR : Rel ?s0 ?t0 |- CR (c_sh_mem_store _ ?w ?ad ?nb ?s0, ?t0) _ =>
      rewrite (sh_mem_store_eq w ad nb s0 HS); split; [reflexivity|apply Rel_sh_mem_store, HR]
  end.

Ltac destruct_match :=
  match goal with |- context [match ?x with _ => _ end] => destruct x eqn:? end.

Ltac crush :=
  repeat (classical_decisions;
          first [ finish | sh_tac | mem_tac | sub_cr
                | progress cbn beta iota zeta delta [c_fix_clock fix_clock fst snd]
                | destruct_match ]).

Lemma evaluate_c_sound cf : LowerSound cf -> forall p, Sound cf p.
Proof.
  intros Hlow p; induction p; intros s0 t0 HR;
    rewrite c_evaluate_c_unfold, evaluate_c_unfold; cbn [c_evaluate_body evaluate_body];
    pose proof HR as (HD & HS & G);
    rewrite ?(c_eval_eq s0 t0 HR), ?c_is_valid_value_eq, ?c_lookup_code_eq, ?HD,
      ?(load_byte_eq _ _ _ G);
    crush.
Qed.

Theorem c_evaluate_c_correct cf p s t : Rel s t ->
  CR (c_evaluate_c base md smd cf p s t) (evaluate_c cf p s).
Proof.
  revert p s t; induction cf as [|cf IH]; intros p.
  - apply evaluate_c_sound; intros p0 s0 t0 H; split; [reflexivity|exact H].
  - apply evaluate_c_sound; intros p0 s0 t0 H; apply IH, H.
Qed.

(** [panSem.evaluate] runs with fuel one above the state's clock. *)
Corollary c_evaluate_correct p s t : Rel s t ->
  evaluate (p, s) = fst (c_evaluate_c base md smd (Datatypes.S (N.to_nat (clock s))) p s t).
Proof. intros H; symmetry; apply (c_evaluate_c_correct _ p s t H). Qed.

Theorem c_evaluate_decls_correct ds : forall s t, Rel s t ->
  c_evaluate_decls base md s t ds = evaluate_decls s ds.
Proof.
  induction ds as [|[fi|sh v0 e|eid sh|nm fl] ds IH]; intros s t HR; cbn [c_evaluate_decls evaluate_decls];
    try reflexivity.
  - destruct (andb _ _); [|reflexivity]. apply IH, Rel_set_code, HR.
  - rewrite (c_eval_eq _ t) by (apply Rel_set_locals, HR).
    destruct (eval _ e); [|reflexivity]. classical_decisions.
    destruct (bool_decide _); [|reflexivity]. apply IH, Rel_set_globals, HR.
  - classical_decisions. destruct (andb _ _); [|reflexivity]. apply IH, Rel_set_eshapes, HR.
  - apply IH, HR.
Qed.

End Correct.
