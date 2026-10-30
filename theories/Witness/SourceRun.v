(** One clocked source run that ends in a final foreign call determines
    [panSem.semantics]. *)
From Stdlib Require Import Lia.
From Galette Require Import Base.
From Galette.HOL.src.coretypes Require Import option.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.pancake Require Import panLang.
From Galette.cakeml.pancake.semantics Require Import panSem panProps.
Open Scope N_scope.

Section Run.
Context {a : N} {ffi_t : Type}.

(** Two runs of the same program from the same state that both finish
    before the clock runs out agree on the result and the I/O trace. *)
Lemma finished_runs_agree (p : prog a) (s : state a ffi_t) k1 k2 r1 t1 r2 t2 :
  evaluate (p, set_clock k1 s) = (r1, t1) -> r1 <> SOME TimeOut ->
  evaluate (p, set_clock k2 s) = (r2, t2) -> r2 <> SOME TimeOut ->
  r1 = r2 /\ io_events (ffi t1) = io_events (ffi t2).
Proof.
  revert k1 k2 r1 t1 r2 t2.
  enough (G : forall k1 k2 r1 t1 r2 t2, k1 <= k2 ->
            evaluate (p, set_clock k1 s) = (r1, t1) -> r1 <> SOME TimeOut ->
            evaluate (p, set_clock k2 s) = (r2, t2) ->
            r1 = r2 /\ io_events (ffi t1) = io_events (ffi t2)).
  { intros k1 k2 r1 t1 r2 t2 H1 N1 H2 N2.
    destruct (N.le_ge_cases k1 k2) as [Hk|Hk].
    - exact (G _ _ _ _ _ _ Hk H1 N1 H2).
    - destruct (G _ _ _ _ _ _ Hk H2 N2 H1) as [-> ->]; split; reflexivity. }
  intros k1 k2 r1 t1 r2 t2 Hk H1 N1 H2.
  pose proof (evaluate_add_clock_eq p (set_clock k1 s) r1 t1 (k2 - k1) (conj H1 N1)) as HA.
  cbn [clock set_clock] in HA; rewrite set_clock_set_clock in HA.
  replace (k1 + (k2 - k1)) with k2 in HA by lia.
  rewrite H2 in HA; injection HA as -> ->; split; reflexivity.
Qed.

Theorem semantics_of_final_run (s : state a ffi_t) start k e t :
  evaluate (@panLang.Call a None start [], set_clock k s) = (SOME (FinalFFI e), t) ->
  semantics s start = Terminate (FFI_outcome e) (io_events (ffi t)).
Proof.
  intros run; unfold semantics.
  destruct (classical_dec _) as [[k' Hk']|_].
  - exfalso.
    destruct (evaluate (panLang.Call None start [], set_clock k' s)) as [r' t'] eqn:E.
    cbn [fst] in Hk'.
    assert (Nr : r' <> SOME TimeOut) by (intros ->; exact Hk').
    destruct (finished_runs_agree _ _ _ _ _ _ _ _ run ltac:(discriminate) E Nr) as [<- _].
    exact Hk'.
  - unfold some; destruct (classical_dec _) as [_|Hn].
    + match goal with |- select ?P = _ => assert (Hs : exists x, P x) end.
      { eexists; exists k, t, (SOME (FinalFFI e)), (FFI_outcome e).
        split; [exact run|split; reflexivity]. }
      pose proof (select_spec _ Hs) as (k' & t' & r' & outcome & E & Hr & ->).
      destruct r' as [[| | | |v|eid v|e']|]; try contradiction; subst outcome.
      * destruct (finished_runs_agree _ _ _ _ _ _ _ _ run ltac:(discriminate) E ltac:(discriminate))
          as [Hr _]; discriminate Hr.
      * destruct (finished_runs_agree _ _ _ _ _ _ _ _ run ltac:(discriminate) E ltac:(discriminate))
          as [Hr ->]; injection Hr as ->; reflexivity.
    + exfalso; apply Hn; eexists; exists k, t, (SOME (FinalFFI e)), (FFI_outcome e).
      split; [exact run|split; reflexivity].
Qed.
End Run.
