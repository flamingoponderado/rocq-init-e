From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Stdlib Require Import Lia.
Open Scope N_scope.
Definition InputBlob := list word8.
(** Recurse on the supplied list, so a large SSZ offset never constructs
    a huge unary index. This is extensionally the original getD reader. *)
Fixpoint nthN {A} (i : N) (xs : list A) (default : A) : A :=
 match xs with
 | [] => default
 | x::rest => if i =? 0 then x else nthN (i-1) rest default
 end.
Lemma nthN_eq_nth {A} (xs : list A) (i : N) (default : A) :
 nthN i xs default = nth (N.to_nat i) xs default.
Proof.
 revert i; induction xs as [|x xs IH]; intros i.
 - destruct (N.to_nat i); reflexivity.
 - cbn [nthN]; destruct (N.eqb_spec i 0) as [E|H].
   + subst; reflexivity.
   + rewrite IH.
     assert (E : N.to_nat i = S (N.to_nat (i-1))) by lia.
     rewrite E; reflexivity.
Qed.
