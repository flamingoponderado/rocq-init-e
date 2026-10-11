(** Original InitE/NatE.lean: finite budget or no uniform bound. *)
From Stdlib Require Import NArith.
Open Scope N_scope.
Inductive NatE : Type := finite (steps : N) | infinity.
Definition Allows (budget : NatE) (steps : N) : Prop :=
  match budget with finite bound => steps <= bound | infinity => True end.
Definition Within (budget : NatE) (terminatesAt : N -> Prop) : Prop :=
  exists steps, Allows budget steps /\ terminatesAt steps.
Theorem within_infinity_iff (terminatesAt : N -> Prop) :
  Within infinity terminatesAt <-> exists steps, terminatesAt steps.
Proof. unfold Within, Allows; firstorder. Qed.
