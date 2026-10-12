(** Finite bootstrap clock shifts retain actual finite target termination.
    Original BootstrapComposition.lean: no installed-state assumption is added. *)
From Galette Require Import Base.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem targetProps.
From Galette.cakeml.semantics.ffi Require Import ffi.
Open Scope N_scope.
Section Composition.
Context {S Q F : Type}.
Definition ClockShift (mc : machine_config 64 S Q) (io : ffi_state F)
 (count : N) (before after : S) : Prop :=
 forall k, evaluate mc io (k+count) before = evaluate mc io k after.
Theorem clock_shift_reflexive mc io before : ClockShift mc io 0 before before.
Proof. intros k; rewrite N.add_0_r; reflexivity. Qed.
Theorem clock_shift_compose mc io n m before middle after :
 ClockShift mc io n before middle -> ClockShift mc io m middle after ->
 ClockShift mc io (m+n) before after.
Proof.
 intros Hn Hm k. replace (k+(m+n)) with ((k+m)+n) by lia.
 rewrite Hn, Hm; reflexivity.
Qed.
Theorem identity_interference_shift (mc : machine_config 64 S Q) count :
 next_interfer mc = (fun _ state => state) -> shift_interfer count mc = mc.
Proof.
 intro H; unfold shift_interfer.
 assert (E : shift_seq count (next_interfer mc) = next_interfer mc).
 { rewrite H; reflexivity. }
 rewrite E; destruct mc; reflexivity.
Qed.
Theorem termination_from_clock_shift mc io count before after out events :
 ClockShift mc io count before after ->
 machine_sem mc io after (Terminate out events) ->
 machine_sem mc io before (Terminate out events).
Proof.
 intros Hshift [clock [post [finalFfi [Heval Hevents]]]].
 exists (clock+count),post,finalFfi; split; [rewrite Hshift; exact Heval|exact Hevents].
Qed.
End Composition.
