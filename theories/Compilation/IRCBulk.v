From InitE.Compilation Require FastLookup.
(** Bulk degree/parent queries for ordered worklist partitioning. *)
From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.sort Require Import sorting.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From InitE.Compilation Require Import SparseState.
From InitE.Compilation Require MapArray.
Open Scope N_scope.
Definition eligible k f := filter_v (fun b => b)
 (mapi (fun i _ => match FastLookup.binary_lookup i (MapArray.data (parents f)) with
                   | Some p => i =? p | None => false end)
 (filter_v (fun d => d <? k) (MapArray.data (degree f)))).
Lemma lookup_eligible k f i : lookup i (eligible k f) =
 match lookup i (MapArray.data (degree f)),lookup i (MapArray.data (parents f)) with
 | Some d,Some p => if (d <? k) && (i =? p) then Some true else None
 | _,_ => None
 end.
Proof.
 unfold eligible. rewrite lookup_filter_v,lookup_mapi,lookup_filter_v.
 rewrite FastLookup.binary_lookup_exact.
 destruct (lookup i (MapArray.data (degree f))) as [d|];
 destruct (lookup i (MapArray.data (parents f))) as [p|]; cbn; try reflexivity;
 destruct (d <? k); cbn; try reflexivity; destruct (i =? p); reflexivity.
Qed.
Definition has i t := match FastLookup.binary_lookup i t with Some b => b | None => false end.
Definition enough d f := Nat.leb (N.to_nat d) (MapArray.size (degree f)) &&
 Nat.leb (N.to_nat d) (MapArray.size (parents f)).
Definition partition d k xs (fallback : IM (list N * list N)) : IM (list N * list N) := fun f =>
 if Nat.leb (Nat.div (MapArray.size (degree f)) 2) (List.length xs) then
 if enough d f then
  let choices := eligible k f in
  (M_success (PARTITION (fun i => (d <=? i) || has i choices) xs),f)
 else fallback f
 else fallback f.
Lemma map_bound {A} xs (a : MapArray.array A) i : MapArray.rep xs a ->
 (N.to_nat i < MapArray.size a)%nat -> exists v, lookup i (MapArray.data a) = Some v.
Proof.
 intros [Hlen Hnth] Hbound. rewrite Hnth.
 destruct (List.nth_error xs (N.to_nat i)) as [v|] eqn:E; [eauto|].
 apply List.nth_error_None in E. lia.
Qed.
Lemma map_value {A} xs (a : MapArray.array A) i v : MapArray.rep xs a ->
 lookup i (MapArray.data a) = Some v -> Msub Subscript i xs = M_success v.
Proof.
 intros Hr Hlookup. rewrite <- (MapArray.sub_rep Subscript xs a i Hr).
 unfold MapArray.sub. rewrite FastLookup.binary_lookup_exact,Hlookup. reflexivity.
Qed.
Lemma split_value d k s f : related s f -> enough d f = true -> forall i,
 reg_alloc.split_degree d k i s =
 (M_success ((d <=? i) || has i (eligible k f)),s).
Proof.
 intros Hr Hbounds i. unfold enough in Hbounds.
 apply Bool.andb_true_iff in Hbounds as [Hd Hp].
 apply Nat.leb_le in Hd,Hp.
 unfold reg_alloc.split_degree.
 destruct (N.ltb_spec i d) as [Hlt|Hge].
 - assert (Hdi : (d <=? i) = false) by (apply N.leb_gt; lia).
   rewrite Hdi. cbn [orb].
   destruct (map_bound (degrees s) (degree f) i (r_degree s f Hr) ltac:(lia)) as [dv Ed].
   destruct (map_bound (coalesced s) (parents f) i (r_parents s f Hr) ltac:(lia)) as [pv Ep].
   pose proof (map_value (degrees s) (degree f) i dv (r_degree s f Hr) Ed) as D.
   pose proof (map_value (coalesced s) (parents f) i pv (r_parents s f Hr) Ep) as P.
   unfold reg_alloc.is_not_coalesced,reg_alloc.degrees_sub,reg_alloc.coalesced_sub,
    Marray_sub,st_ex_bind,st_ex_return.
   cbv beta. rewrite D. cbv beta iota. rewrite P. cbv beta iota.
   unfold has. rewrite FastLookup.binary_lookup_exact,lookup_eligible,Ed,Ep.
   destruct ((dv <? k) && (i =? pv)); reflexivity.
 - assert (Hdi : (d <=? i) = true) by (apply N.leb_le; lia).
   rewrite Hdi. reflexivity.
Qed.
Lemma partition_readonly {S A E} (p : A -> M S bool E) b xs : forall tt_ ff s,
 (forall i, p i s = (M_success (b i),s)) ->
 st_ex_PARTITION p xs tt_ ff s = (M_success (PART b xs tt_ ff),s).
Proof.
 induction xs as [|x xs IH]; intros tt_ ff s H; [reflexivity|].
 cbn [st_ex_PARTITION PART]. unfold st_ex_bind at 1. rewrite H.
 cbv beta iota. destruct (b x); apply IH; exact H.
Qed.
Theorem partition_sim d k xs fallback :
 sim (st_ex_PARTITION (reg_alloc.split_degree d k) xs [] []) fallback ->
 sim (st_ex_PARTITION (reg_alloc.split_degree d k) xs [] []) (partition d k xs fallback).
Proof.
 intros H s f Hr. unfold partition.
 destruct (Nat.leb (Nat.div (MapArray.size (degree f)) 2) (List.length xs)); [|apply H; exact Hr].
 destruct (enough d f) eqn:E.
 - rewrite (partition_readonly (reg_alloc.split_degree d k)
    (fun i => (d <=? i) || has i (eligible k f)) xs [] [] s (split_value d k s f Hr E)).
   split; [reflexivity|exact Hr].
 - apply H; exact Hr.
Qed.
