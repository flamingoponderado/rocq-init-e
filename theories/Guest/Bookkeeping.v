(** Fixed source startup words: original Guest/Bookkeeping.lean. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
Open Scope N_scope.
Definition startupHeaders : list (word 64) :=
 [n2w 2684485656; n2w 2684522568; n2w 2684522568; n2w 2148392340; n2w 2148392960].
