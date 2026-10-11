(** Original InitE/TargetTotality.lean, using Galette's proved totality. *)
From Galette Require Import Base.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem targetProps.
Section Totality.
Context {S Q F : Type}.
Theorem target_has_behaviour (mc : machine_config 64 S Q)
 (st : ffi_state F) (ms : S) : exists b, machine_sem mc st ms b.
Proof. apply machine_sem_total. Qed.
Theorem target_termination_of_behaviour_eq (mc : machine_config 64 S Q)
 (st : ffi_state F) (ms : S) (out : outcome) (events : list io_event) :
 (forall b, machine_sem mc st ms b -> b = Terminate out events) ->
 machine_sem mc st ms (Terminate out events).
Proof.
 intros H; destruct (target_has_behaviour mc st ms) as [b HB].
 rewrite <- (H b HB); exact HB.
Qed.
End Totality.
