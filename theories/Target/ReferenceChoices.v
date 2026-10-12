(** Original Flapjack Misc/Option.lean: THE NONE is a separate opaque
    value for each inhabited carrier, independent in the proof interface
    from HolArb. The opaque witness introduces no new axiom. *)
From Galette Require Import Base.
Definition theNone {A : Type} `{Inhabited A} : A.
Proof. exact ARB. Qed.
Definition referenceThe {A : Type} `{Inhabited A} (value : option A) : A :=
 match value with Some x => x | None => theNone end.
Theorem reference_the_some {A : Type} `{Inhabited A} (x : A) : referenceThe (Some x) = x.
Proof. reflexivity. Qed.
Theorem reference_the_none {A : Type} `{Inhabited A} : referenceThe (None : option A) = theNone.
Proof. reflexivity. Qed.
