(** Fixed source startup words for the software guest ROM. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
Open Scope N_scope.
Definition startupHeaders : list (word 64) :=
 [n2w 2684485656; n2w 2684522480; n2w 2684522480; n2w 2148466996; n2w 2148470784].
