(** A runner for the software guest on arbitrary inputs.

    [runInput clock len input] evaluates the guest with the computable
    evaluator and reports how the run ended, the clock it used and the first
    [len] output bytes.  [runInput_halted] shows that a [Halted] report is the
    source behaviour of [input] and that the reported bytes are its output.
    [tools/eest-runner] extracts it to OCaml. *)
From Stdlib Require Import FMapPositive List.
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.string Require Import string.
From Galette.HOL.src.finite_maps Require Import finite_map.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.pancake Require Import panLang.
From Galette.cakeml.pancake.semantics Require Import panSem.
From InitE.Guest Require Import Ast Basic HostMemory.
From InitE.InitE Require Import Parameters SourceSemantics Observations.
From InitE.Witness Require Import Evaluator EvaluatorCorrect SourceDomains SourceRun.
Open Scope N_scope.
Open Scope hol_string_scope.

Definition emptyTrie : WordTrie.t (V := word_lab 64) := PositiveMap.empty _.

Definition mainCall : prog 64 := panLang.Call None (strlit "main") [].

Inductive runOutcome :=
| Halted (configuration bytes : list word8)
| Trapped (configuration : list word8)
| OtherFinal (event : final_event)
| TimedOut
| Failed.

Record report := {
  outcome : runOutcome;
  clockUsed : N;
  eventCount : N;
  output : list word8 }.

Definition classify (r : option (result 64)) : runOutcome :=
  match r with
  | Some (FinalFFI (Final_event (ffi.ExtCall name) configuration bytes FFI_failed)) =>
      if bool_decide (name = strlit "halt") then Halted configuration bytes
      else if bool_decide (name = strlit "trap") then Trapped configuration
      else OtherFinal (Final_event (ffi.ExtCall name) configuration bytes FFI_failed)
  | Some (FinalFFI e) => OtherFinal e
  | Some TimeOut => TimedOut
  | _ => Failed
  end.

(** [outputByte] at offset [i], without the offset bound. *)
Definition observedByte (input : InputBlob) (host : HostMemory) (i : N) : word8 :=
  match host (n2w outputStart+n2w i)%w with Some value => value | None => n2w 0 end.

Definition outputBytes (input : InputBlob) (events : list io_event) (len : nat) : list word8 :=
  let host := observedHost input events in
  List.map (fun i => observedByte input host (N.of_nat i)) (List.seq 0 len).

Definition runInput (clock : N) (len : nat) (input : InputBlob) : report :=
  match decs_stcnames [] guestAst with
  | None => {| outcome := Failed; clockUsed := 0; eventCount := 0; output := [] |}
  | Some st =>
      match c_evaluate_decls sourceMemory ordinaryDecider
              (set_structs st (sourceInitialState input)) emptyTrie guestAst with
      | None => {| outcome := Failed; clockUsed := 0; eventCount := 0; output := [] |}
      | Some s =>
          let '(r, t, _) := c_evaluate_c sourceMemory ordinaryDecider sharedDecider
                              (Datatypes.S (N.to_nat clock)) mainCall (set_clock clock s) emptyTrie in
          let events := List.rev (io_events (ffi t)) in
          {| outcome := classify r; clockUsed := clock - panSem.clock t;
             eventCount := N.of_nat (List.length events);
             output := outputBytes input events len |}
      end
  end.

Lemma Rel_initial input st :
  Rel sourceMemory ordinaryDomain sharedDomain (set_structs st (sourceInitialState input)) emptyTrie.
Proof.
  split; [reflexivity|split; [reflexivity|]].
  intros x; unfold WordTrie.get; rewrite PositiveMap.gempty; reflexivity.
Qed.

Lemma Rel_decls ds : forall (s s' : state 64 HostMemory),
  Rel sourceMemory ordinaryDomain sharedDomain s emptyTrie ->
  evaluate_decls s ds = Some s' -> Rel sourceMemory ordinaryDomain sharedDomain s' emptyTrie.
Proof.
  induction ds as [|[fi|sh v0 e|eid sh|nm fl] ds IH]; intros s s' HR E; cbn [evaluate_decls] in E.
  - injection E as <-; exact HR.
  - destruct (andb _ _); [|discriminate]. eapply IH; [apply Rel_set_code, HR|exact E].
  - destruct (eval _ e); [|discriminate]. destruct (bool_decide _); [|discriminate].
    eapply IH; [apply Rel_set_globals, HR|exact E].
  - destruct (andb _ _); [|discriminate]. eapply IH; [apply Rel_set_eshapes, HR|exact E].
  - exact (IH s s' HR E).
Qed.

Lemma evaluate_decls_ffi ds : forall (s s' : state 64 HostMemory),
  evaluate_decls s ds = Some s' -> ffi s' = ffi s.
Proof.
  induction ds as [|[fi|sh v0 e|eid sh|nm fl] ds IH]; intros s s' E; cbn [evaluate_decls] in E.
  - injection E as <-; reflexivity.
  - destruct (andb _ _); [|discriminate]. exact (IH _ _ E).
  - destruct (eval _ e); [|discriminate]. destruct (bool_decide _); [|discriminate]. exact (IH _ _ E).
  - destruct (andb _ _); [|discriminate]. exact (IH _ _ E).
  - exact (IH _ _ E).
Qed.

Lemma outputBytes_nth input events len offset :
  (N.to_nat (offsetValue offset) < len)%nat ->
  outputByte input events offset =
  List.nth (N.to_nat (offsetValue offset)) (outputBytes input events len) (n2w 0).
Proof.
  intros H; unfold outputBytes; cbv zeta.
  set (f := fun i => observedByte input (observedHost input events) (N.of_nat i)).
  rewrite (List.nth_indep _ (n2w 0) (f 0%nat))
    by (rewrite List.length_map, List.length_seq; exact H).
  rewrite List.map_nth, List.seq_nth by exact H; unfold f; cbn [Nat.add].
  rewrite N2Nat.id; reflexivity.
Qed.

(** A [Halted] report is the source behaviour, and its bytes are the output. *)
Theorem runInput_halted clock len input configuration bytes :
  outcome (runInput clock len input) = Halted configuration bytes ->
  exists events,
    sourceBehaviour input =
      Terminate (FFI_outcome (Final_event (ffi.ExtCall (strlit "halt")) configuration bytes FFI_failed))
        events /\
    forall offset, (N.to_nat (offsetValue offset) < len)%nat ->
      outputByte input events offset =
      List.nth (N.to_nat (offsetValue offset)) (output (runInput clock len input)) (n2w 0).
Proof.
  unfold runInput, sourceBehaviour, semantics_decls.
  destruct (decs_stcnames [] guestAst) as [st|]; [|discriminate].
  pose proof (Rel_initial input st) as HR0.
  rewrite <- (c_evaluate_decls_correct sourceMemory ordinaryDecider
    ordinaryDomain sharedDomain ordinaryDecider_spec guestAst _ _ HR0).
  destruct (c_evaluate_decls _ _ _ _ guestAst) as [s|] eqn:Hdecls; [|discriminate].
  rewrite (c_evaluate_decls_correct sourceMemory ordinaryDecider
    ordinaryDomain sharedDomain ordinaryDecider_spec guestAst _ _ HR0) in Hdecls.
  pose proof (Rel_set_clock sourceMemory ordinaryDomain sharedDomain clock _ _
    (Rel_decls _ _ _ HR0 Hdecls)) as HR.
  pose proof (c_evaluate_correct sourceMemory ordinaryDecider sharedDecider
    ordinaryDomain sharedDomain ordinaryDecider_spec sharedDecider_spec
    mainCall _ _ HR) as run.
  rewrite norm_id in run by (cbn [ffi set_clock]; rewrite (evaluate_decls_ffi _ _ _ Hdecls); reflexivity).
  cbn [panSem.clock set_clock] in run.
  revert run.
  destruct (c_evaluate_c _ _ _ _ _ _ _) as [[r t] tt]; cbn [fst outcome output]; intros run.
  unfold classify.
  destruct r as [[| | | | | |[[name|] conf bs result]]|]; try discriminate.
  destruct result; [|discriminate].
  destruct (bool_decide (name = strlit "halt")) eqn:Eh;
    [|destruct (bool_decide (name = strlit "trap")); discriminate].
  apply bool_decide_spec in Eh; subst name.
  intros C; injection C as -> ->.
  cbn [snd] in run.
  exists (List.rev (io_events (ffi t))); split.
  - exact (semantics_of_final_run _ _ clock _ _ run).
  - intros offset H; apply outputBytes_nth, H.
Qed.
