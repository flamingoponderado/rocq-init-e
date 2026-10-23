From InitE.Compilation Require FastLookup.
(** A finite list array represented by a sparse map, with exact exceptions. *)
From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From InitE.Compilation Require FastGraph.
From Stdlib Require Import List.
Import ListNotations.
Open Scope N_scope.
Fixpoint encode_from {A} (k : N) (xs : list A) : num_map A :=
 match xs with [] => LN | x::xs => insert k x (encode_from (k+1) xs) end.
Lemma encode_lookup {A} (xs : list A) : forall k i,
 lookup i (encode_from k xs) =
 if k <=? i then nth_error xs (N.to_nat (i-k)) else None.
Proof.
 induction xs as [|x xs IH]; intros k i; cbn [encode_from].
 - rewrite lookup_LN. destruct (k <=? i); [destruct (N.to_nat (i-k))|]; reflexivity.
 - rewrite lookup_insert,IH. destruct (decide (i=k)) as [->|Hne].
   + rewrite N.leb_refl,N.sub_diag. reflexivity.
   + destruct (N.leb_spec k i) as [Hle|Hlt].
     * assert (Hnext : (k+1 <=? i) = true) by (apply N.leb_le; lia).
       rewrite Hnext. replace (N.to_nat (i-k)) with (S (N.to_nat (i-(k+1)))) by lia. reflexivity.
     * assert (Hnext : (k+1 <=? i) = false) by (apply N.leb_gt; lia).
       rewrite Hnext. reflexivity.
Qed.
Record array (A : Type) := Array { size : nat; data : num_map A }.
Arguments Array {A} _ _.
Arguments size {A} _.
Arguments data {A} _.
Definition rep {A} (xs : list A) (a : array A) :=
 List.length xs = size a /\ forall i, lookup i (data a) = nth_error xs (N.to_nat i).
Definition encode {A} (xs : list A) := Array (List.length xs) (encode_from 0 xs).
Lemma encode_rep {A} (xs : list A) : rep xs (encode xs).
Proof.
 split; [reflexivity|]. intro i. change (lookup i (encode_from 0 xs) = nth_error xs (N.to_nat i)).
 rewrite encode_lookup,N.sub_0_r.
 assert (H : (0 <=? i) = true) by (apply N.leb_le; lia). rewrite H; reflexivity.
Qed.
Definition sub {A E} (e : E) i (a : array A) : exc A E :=
 match FastLookup.binary_lookup i (data a) with Some v => M_success v | None => M_failure e end.
Definition update {A E} (e : E) v i (a : array A) : exc (array A) E :=
 match FastLookup.binary_lookup i (data a) with
 | Some _ => M_success (Array (size a) (insert i v (data a)))
 | None => M_failure e
 end.
Lemma sub_rep {A E} (e : E) (xs : list A) a i : rep xs a -> sub e i a = Msub e i xs.
Proof. intros [_ H]; unfold sub; rewrite FastLookup.binary_lookup_exact,FastGraph.Msub_nth,H; reflexivity. Qed.
Definition results {A E} (x : exc (list A) E) (y : exc (array A) E) :=
 match x,y with
 | M_success xs,M_success a => rep xs a
 | M_failure e,M_failure e' => e=e'
 | _,_ => False
 end.
Lemma update_rep {A E} (e : E) (v : A) i xs a : rep xs a ->
 results (Mupdate e v i xs) (update e v i a).
Proof.
 intros [Hlen Hnth]. unfold update. rewrite FastLookup.binary_lookup_exact,Hnth.
 destruct (Mupdate e v i xs) as [ys|err] eqn:Eup.
 - destruct (FastGraph.Mupdate_has_index e v xs i ys Eup) as [old Hpresent].
   rewrite Hpresent. cbn [results].
   destruct (FastGraph.Mupdate_success e v xs i ys Eup) as [Hlen' Hnth'].
   split; [cbn; congruence|]. intro j. cbn [data]. rewrite lookup_insert,Hnth,Hnth'.
   destruct (decide (j=i)),(N.eqb_spec j i); try congruence; reflexivity.
 - destruct (FastGraph.Mupdate_failure e v xs i err Eup) as [-> Hnone].
   rewrite Hnone. reflexivity.
Qed.
Fixpoint decode_from {A} (default : A) n k (a : num_map A) : list A :=
 match n with O => [] | S n =>
 (match FastLookup.binary_lookup k a with Some v => v | None => default end) :: decode_from default n (k+1) a end.
Definition decode {A} (default : A) (a : array A) := decode_from default (size a) 0 (data a).
Lemma decode_from_rep {A} (xs : list A) : forall default k a,
 (forall i, lookup (k+N.of_nat i) a = nth_error xs i) ->
 decode_from default (List.length xs) k a = xs.
Proof.
 induction xs as [|x xs IH]; intros default k a H; [reflexivity|].
 cbn [List.length decode_from]. specialize (H O) as H0; cbn in H0; rewrite N.add_0_r in H0.
 rewrite FastLookup.binary_lookup_exact,H0. f_equal. apply IH. intro i. specialize (H (S i)).
 replace (k+1+N.of_nat i) with (k+N.of_nat (S i)) by lia. exact H.
Qed.
Lemma decode_rep {A} (default : A) xs a : rep xs a -> decode default a = xs.
Proof.
 intros [Hlen Hnth]. unfold decode. rewrite <- Hlen. apply decode_from_rep.
 intro i. rewrite N.add_0_l,Hnth,Nat2N.id. reflexivity.
Qed.
