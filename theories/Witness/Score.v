(** Every certified score is at least 3.

    The source semantics accepts the witness [Witness.Input.input]: the
    computable evaluator, run by [vm_compute] at clock 32000, halts through
    [halt] with output byte 32 set, and [EvaluatorCorrect] and [SourceRun]
    turn that run into [sourceBehaviour input].  [TargetLowerBound] then
    shows that a target run matching it needs at least three ticks. *)
From Stdlib Require Import FMapPositive.
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.string Require Import string.
From Galette.HOL.src.finite_maps Require Import finite_map.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.pancake Require Import panLang.
From Galette.cakeml.pancake.semantics Require Import panSem.
From InitE.Guest Require Import Ast GasLimit HostMemory.
From InitE.InitE Require Import NatE Parameters SubmissionModel SourceSemantics Observations Challenge.
From InitE.Witness Require Import Evaluator EvaluatorCorrect SourceDomains SourceRun Input
  TargetLowerBound Runner.
Open Scope N_scope.
Open Scope hol_string_scope.

Definition witnessClock : N := 32000.

(** The run's result is accepted: a final [halt] call with output byte 32 set. *)
Definition acceptedRun (c : @cres 64 HostMemory) : bool :=
  match c with
  | (Some (FinalFFI (Final_event (ffi.ExtCall name) [] [] FFI_failed)), s, _) =>
      bool_decide (name = strlit "halt") &&
      (w2n (outputByte input (io_events (ffi s)) acceptanceOffset) =? 1)
  | _ => false
  end.

(** The only computation: about 200 s of [vm_compute].  It is stated over
    [decs_stcnames] and [c_evaluate_decls] themselves so that using it needs
    no conversion through the run. *)
Lemma witness_check :
  match decs_stcnames [] guestAst with
  | None => false
  | Some st =>
      match c_evaluate_decls sourceMemory ordinaryDecider
              (set_structs st (sourceInitialState input)) emptyTrie guestAst with
      | None => false
      | Some s =>
          acceptedRun (c_evaluate_c sourceMemory ordinaryDecider sharedDecider
                         (Datatypes.S (N.to_nat witnessClock)) mainCall
                         (set_clock witnessClock s) emptyTrie)
      end
  end = true.
Proof. vm_compute; reflexivity. Qed.

Definition haltEvent : final_event := Final_event (ffi.ExtCall (strlit "halt")) [] [] FFI_failed.

Theorem witness_behaviour : exists events,
  sourceBehaviour input = Terminate (FFI_outcome haltEvent) events /\
  outputByte input events acceptanceOffset = n2w 1.
Proof.
  pose proof witness_check as C; revert C.
  change (sourceBehaviour input) with
    (semantics_decls (sourceInitialState input) (strlit "main") guestAst).
  unfold semantics_decls.
  destruct (decs_stcnames [] guestAst) as [st|]; [|discriminate].
  pose proof (Rel_initial input st) as HR0.
  rewrite <- (c_evaluate_decls_correct sourceMemory ordinaryDecider
    ordinaryDomain sharedDomain ordinaryDecider_spec guestAst _ _ HR0).
  destruct (c_evaluate_decls _ _ _ _ guestAst) as [s|] eqn:Hdecls; [|discriminate].
  rewrite (c_evaluate_decls_correct sourceMemory ordinaryDecider
    ordinaryDomain sharedDomain ordinaryDecider_spec guestAst _ _ HR0) in Hdecls.
  pose proof (Rel_set_clock sourceMemory ordinaryDomain sharedDomain witnessClock _ _
    (Rel_decls _ _ _ HR0 Hdecls)) as HR.
  pose proof (c_evaluate_correct sourceMemory ordinaryDecider sharedDecider
    ordinaryDomain sharedDomain ordinaryDecider_spec sharedDecider_spec
    mainCall _ _ HR) as run.
  cbn [clock set_clock] in run.
  revert run.
  destruct (c_evaluate_c _ _ _ _ _ _ _) as [[r t] tt]; cbn [fst]; intros run.
  unfold acceptedRun.
  destruct r as [[| | | | | |[[name|] conf bytes outcome]]|]; try discriminate.
  destruct conf; [|discriminate]. destruct bytes; [|discriminate].
  destruct outcome; [|discriminate].
  intros C; apply Bool.andb_true_iff in C as [Hname Hbyte].
  apply bool_decide_spec in Hname; subst name.
  exists (io_events (ffi t)); split.
  - exact (semantics_of_final_run _ _ witnessClock _ _ run).
  - apply N.eqb_eq in Hbyte. apply word_eq_w2n. rewrite Hbyte. reflexivity.
Qed.

Lemma witness_gas : declaredGasLimit input <= 200000000.
Proof. vm_compute; discriminate. Qed.

Lemma witness_initially_clear : outputByte input [] acceptanceOffset <> n2w 1.
Proof. intros E; apply (f_equal w2n) in E; vm_compute in E; discriminate E. Qed.

Lemma halt_covered : coveredOutcome (FFI_outcome haltEvent).
Proof. split; [reflexivity|left; discriminate]. Qed.

Theorem certificate_score_at_least_three {s claimed} (certificate : Certificate s claimed) :
  Allows claimed 3.
Proof.
  destruct witness_behaviour as (events & source & accepted).
  exact (score_at_least_three_of_accepted certificate input witness_gas witness_initially_clear
    _ events source halt_covered (conj (conj eq_refl eq_refl) accepted)).
Qed.

Theorem certificate_finite_score_at_least_three {s k} (certificate : Certificate s (finite k)) :
  3 <= k.
Proof. exact (certificate_score_at_least_three certificate). Qed.

Theorem submission_score_at_least_three {s claimed} (certificate : Certificate s claimed) :
  Allows (K s) 3.
Proof. rewrite (score s claimed certificate); exact (certificate_score_at_least_three certificate). Qed.
