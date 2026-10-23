(** Binary trie traversal, exactly equal to the arithmetic lookup. *)
From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.list.src Require Import list rich_list.
Open Scope N_scope.
Fixpoint lookup_pos {A} (p : positive) (t : spt A) : option A :=
 match t with
 | LN => None
 | LS a => match p with xH => Some a | _ => None end
 | BN l r => match p with xH => None | xI q => lookup_pos q l | xO q => lookup_pos q r end
 | BS l a r => match p with xH => Some a | xI q => lookup_pos q l | xO q => lookup_pos q r end
 end.
Definition binary_lookup {A} k (t : spt A) := lookup_pos (N.succ_pos k) t.
Lemma binary_lookup_exact {A} (t : spt A) : forall k, binary_lookup k t = lookup k t.
Proof.
 induction t as [|a|l IHl r IHr|l IHl a r IHr]; intro k;
 unfold binary_lookup in *; bitcase k;
 rewrite ?succ_pos_0,?succ_pos_odd,?succ_pos_even;
 cbn [lookup_pos]; spt_simp; rewrite ?IHl,?IHr; reflexivity.
Qed.
