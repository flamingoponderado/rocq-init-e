From InitE.Compilation Require FastLookup.
(** Exact graph construction using a sparse outer adjacency array.
    Neighbour lists and the order of every read/write are unchanged. *)
From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Stdlib Require Import List.
Import ListNotations.
Open Scope N_scope.

Fixpoint encode_from (k : N) (xs : list (list N)) : num_map (list N) :=
 match xs with [] => LN | x::xs => insert k x (encode_from (k+1) xs) end.
Definition encode xs := encode_from 0 xs.
Record arrayState := ArrayState { arrayLength : nat; arrayData : num_map (list N) }.
Definition represents (xs : list (list N)) (a : arrayState) :=
 List.length xs = arrayLength a /\
 forall i, lookup i (arrayData a) = nth_error xs (N.to_nat i).

Lemma encode_lookup xs : forall k i,
 lookup i (encode_from k xs) =
 if k <=? i then nth_error xs (N.to_nat (i-k)) else None.
Proof.
 induction xs as [|x xs IH]; intros k i; cbn [encode_from].
 - rewrite lookup_LN. destruct (k <=? i); [destruct (N.to_nat (i-k))|]; reflexivity.
 - rewrite lookup_insert, IH.
   destruct (decide (i = k)) as [->|Hne].
   + rewrite N.leb_refl, N.sub_diag. reflexivity.
   + destruct (N.leb_spec k i) as [Hle|Hlt].
     * assert (Hnext : (k+1 <=? i) = true) by (apply N.leb_le; lia).
       rewrite Hnext.
       replace (N.to_nat (i-k)) with (S (N.to_nat (i-(k+1)))) by lia.
       reflexivity.
     * assert (Hnext : (k+1 <=? i) = false) by (apply N.leb_gt; lia).
       rewrite Hnext. reflexivity.
Qed.
Lemma represents_encode xs : represents xs (ArrayState (List.length xs) (encode xs)).
Proof. split; [reflexivity|]. intro i; change (lookup i (encode_from 0 xs) = nth_error xs (N.to_nat i)).
 rewrite encode_lookup, N.sub_0_r.
 assert ((0 <=? i) = true) by (apply N.leb_le; lia). rewrite H; reflexivity. Qed.

Definition read (i : N) : M arrayState (list N) state_exn := fun a =>
 (match FastLookup.binary_lookup i (arrayData a) with Some x => M_success x | None => M_failure Subscript end,a).
Definition write (i : N) (v : list N) : M arrayState unit state_exn := fun a =>
 match FastLookup.binary_lookup i (arrayData a) with
 | None => (M_failure Subscript,a)
 | Some _ => (M_success tt,ArrayState (arrayLength a) (insert i v (arrayData a)))
 end.

Lemma Msub_nth {A E} (e : E) (xs : list A) : forall i,
 Msub e i xs = match nth_error xs (N.to_nat i) with
 | Some x => M_success x | None => M_failure e end.
Proof.
 induction xs as [|x xs IH]; intro i; cbn [Msub].
 - destruct (N.to_nat i); reflexivity.
 - destruct (N.eqb_spec i 0) as [->|Hne]; [reflexivity|].
   replace (N.to_nat i) with (S (N.to_nat (i-1))) by lia.
   cbn [nth_error]. apply IH.
Qed.

Lemma Mupdate_success {A E} (e : E) (v : A) (xs : list A) : forall i ys,
 Mupdate e v i xs = M_success ys ->
 List.length ys = List.length xs /\
 forall j, nth_error ys (N.to_nat j) =
 if j =? i then Some v else nth_error xs (N.to_nat j).
Proof.
 induction xs as [|x xs IH]; intros i ys H; cbn [Mupdate] in H; [discriminate|].
 destruct (N.eqb_spec i 0) as [->|Hi].
 - inversion H; subst ys. split; [reflexivity|]. intro j.
   destruct (N.eqb_spec j 0) as [->|Hj]; [reflexivity|].
   replace (N.to_nat j) with (S (N.to_nat (j-1))) by lia. reflexivity.
 - destruct (Mupdate e v (i-1) xs) as [zs|err] eqn:Eup; [|discriminate].
   inversion H; subst ys. destruct (IH _ _ Eup) as [Hlen Hnth].
   split; [cbn; congruence|]. intro j.
   destruct (N.eqb_spec j 0) as [->|Hj].
   + assert (Ez : (0 =? i) = false) by (apply N.eqb_neq; lia). rewrite Ez. reflexivity.
   + replace (N.to_nat j) with (S (N.to_nat (j-1))) by lia.
     cbn [nth_error]. rewrite Hnth.
     destruct (N.eqb_spec (j-1) (i-1)), (N.eqb_spec j i); try lia; reflexivity.
Qed.
Lemma Mupdate_failure {A E} (e : E) (v : A) (xs : list A) : forall i err,
 Mupdate e v i xs = M_failure err -> err = e /\ nth_error xs (N.to_nat i) = None.
Proof.
 induction xs as [|x xs IH]; intros i err H; cbn [Mupdate] in H.
 - inversion H; subst. split; [reflexivity|]. destruct (N.to_nat i); reflexivity.
 - destruct (N.eqb_spec i 0) as [->|Hi]; [discriminate|].
   destruct (Mupdate e v (i-1) xs) as [zs|err'] eqn:Eup; [discriminate|].
   inversion H; subst err'. destruct (IH _ _ Eup) as [-> Hnone].
   split; [reflexivity|]. replace (N.to_nat i) with (S (N.to_nat (i-1))) by lia.
   exact Hnone.
Qed.
Lemma Mupdate_present {A E} (e : E) (v : A) (xs : list A) : forall i old,
 nth_error xs (N.to_nat i) = Some old -> exists ys, Mupdate e v i xs = M_success ys.
Proof.
 intros i old H. destruct (Mupdate e v i xs) as [ys|err] eqn:Eup; [eauto|].
 apply Mupdate_failure in Eup. destruct Eup as [_ Hnone]; congruence.
Qed.

Lemma Mupdate_has_index {A E} (e : E) (v : A) (xs : list A) : forall i ys,
 Mupdate e v i xs = M_success ys -> exists old, nth_error xs (N.to_nat i) = Some old.
Proof.
 induction xs as [|x xs IH]; intros i ys H; cbn [Mupdate] in H; [discriminate|].
 destruct (N.eqb_spec i 0) as [->|Hi]; [exists x; reflexivity|].
 destruct (Mupdate e v (i-1) xs) as [zs|err] eqn:Eup; [|discriminate].
 replace (N.to_nat i) with (S (N.to_nat (i-1))) by lia.
 cbn [nth_error]. eapply IH; exact Eup.
Qed.

Definition withAdj (xs : list (list N)) (s : ra_state) : ra_state :=
 mk_ra_state xs (node_tag s) (degrees s) (dim s) (simp_wl s) (spill_wl s)
 (freeze_wl s) (avail_moves_wl s) (unavail_moves_wl s) (coalesced s)
 (move_related s) (stack s).
Lemma withAdj_twice xs ys s : withAdj xs (withAdj ys s) = withAdj xs s.
Proof. reflexivity. Qed.
Lemma withAdj_self s : withAdj (adj_ls s) s = s.
Proof. destruct s; reflexivity. Qed.

Section Simulation.
Variable base : ra_state.
Definition related (s : ra_state) (a : arrayState) :=
 exists xs, s = withAdj xs base /\ represents xs a.
Definition sim {A} (p : RA A) (q : M arrayState A state_exn) :=
 forall s a, related s a ->
 fst (p s) = fst (q a) /\ related (snd (p s)) (snd (q a)).

Lemma sim_return {A} (v : A) : sim (st_ex_return v) (st_ex_return v).
Proof. intros s a H; split; [reflexivity|exact H]. Qed.
Lemma sim_bind {A B} (p : RA A) (q : M arrayState A state_exn)
 (f : A -> RA B) (g : A -> M arrayState B state_exn) :
 sim p q -> (forall v, sim (f v) (g v)) -> sim (st_ex_bind p f) (st_ex_bind q g).
Proof.
 intros Hp Hf s a Hr. specialize (Hp s a Hr).
 unfold st_ex_bind.
 destruct (p s) as [r s'] eqn:Ep; destruct (q a) as [r' a'] eqn:Eq.
 cbn [fst snd] in Hp. destruct Hp as [<- Hr']. destruct r as [v|e].
 - apply Hf; exact Hr'.
 - split; [reflexivity|exact Hr'].
Qed.
Lemma sim_ignore {A B} (p : RA A) (q : M arrayState A state_exn)
 (f : RA B) (g : M arrayState B state_exn) :
 sim p q -> sim f g -> sim (st_ex_ignore_bind p f) (st_ex_ignore_bind q g).
Proof. intros H H'; apply sim_bind with (f := fun _ => f) (g := fun _ => g); auto. Qed.

Lemma sim_read i : sim (adj_ls_sub i) (read i).
Proof.
 intros s a [xs [-> [Hlen Hnth]]].
 unfold adj_ls_sub, Marray_sub, read. cbn [adj_ls withAdj].
 rewrite FastLookup.binary_lookup_exact, Msub_nth, Hnth. split; [reflexivity|].
 exists xs; split; [reflexivity|split; assumption].
Qed.
Lemma sim_write i v : sim (update_adj_ls i v) (write i v).
Proof.
 intros s a [xs [-> [Hlen Hnth]]].
 unfold update_adj_ls, Marray_update, write. cbn [adj_ls withAdj].
 rewrite FastLookup.binary_lookup_exact, Hnth.
 destruct (nth_error xs (N.to_nat i)) as [old|] eqn:Enth.
 - destruct (Mupdate_present Subscript v xs i old Enth) as [ys Eup].
   rewrite Eup. cbn [fst snd]. split; [reflexivity|].
   destruct (Mupdate_success Subscript v xs i ys Eup) as [Hlen' Hnth'].
   exists ys; split; [reflexivity|]. split; [cbn; congruence|]. intro j.
   cbn [arrayData]. rewrite lookup_insert,Hnth,Hnth'.
   destruct (decide (j=i)), (N.eqb_spec j i); try congruence; reflexivity.
 - destruct (Mupdate Subscript v i xs) as [ys|err] eqn:Eup.
   + destruct (Mupdate_has_index Subscript v xs i ys Eup) as [old Ho]; congruence.
   + destruct (Mupdate_failure Subscript v xs i err Eup) as [-> _].
     cbn [fst snd]. split; [reflexivity|]. exists xs; split; [reflexivity|split; assumption].
Qed.
End Simulation.

(** Structural insertion avoids the quadratic [List.rev] of the original
    accumulator-based implementation, preserving the exact list order. *)
Fixpoint sortedInsert (x : N) (l : list N) : list N :=
 match l with
 | [] => [x]
 | y::ys => if x =? y then y::ys else if y <? x then x::y::ys else y::sortedInsert x ys
 end.
Lemma sorted_insert_acc x l : forall acc,
 sorted_insert x acc l = List.rev acc ++ sortedInsert x l.
Proof.
 induction l as [|y ys IH]; intro acc; cbn [sorted_insert sortedInsert].
 - reflexivity.
 - destruct (x =? y), (y <? x); try reflexivity.
   rewrite IH. cbn [List.rev]. rewrite <- app_assoc. reflexivity.
Qed.
Lemma sortedInsert_exact x l : sortedInsert x l = sorted_insert x [] l.
Proof. rewrite sorted_insert_acc. reflexivity. Qed.

Open Scope monad_scope.
Definition insertEdge (x y : N) : M arrayState unit state_exn :=
 adjx <- read x ;;
 adjy <- read y ;;
 write x (sortedInsert y adjx) ;;
 write y (sortedInsert x adjy).
Fixpoint listInsertEdge (x : N) (l : list N) : M arrayState unit state_exn :=
 match l with [] => st_ex_return tt | y::ys => insertEdge x y ;; listInsertEdge x ys end.
Fixpoint cliqueInsertEdge (l : list N) : M arrayState unit state_exn :=
 match l with [] => st_ex_return tt | x::xs => listInsertEdge x xs ;; cliqueInsertEdge xs end.
Fixpoint extendClique (l cli : list N) : M arrayState (list N) state_exn :=
 match l with
 | [] => st_ex_return cli
 | x::xs => if list.MEM x cli then extendClique xs cli
            else listInsertEdge x cli ;; extendClique xs (x::cli)
 end.
Fixpoint buildGraph (ta : N -> N) (ct : clash_tree) (liveout : list N)
 : M arrayState (list N) state_exn :=
 match ct with
 | Delta w r =>
   wta <- st_ex_return (list.MAP ta w) ;;
   rta <- st_ex_return (list.MAP ta r) ;;
   live <- extendClique wta liveout ;;
   live <- st_ex_return (list.FILTER (fun x => negb (list.MEM x wta)) live) ;;
   livein <- extendClique rta live ;;
   st_ex_return livein
 | Set_ t =>
   live <- st_ex_return (list.MAP ta (list.MAP fst (toAList t))) ;;
   cliqueInsertEdge live ;;
   st_ex_return live
 | Branch topt t1 t2 =>
   t1_live <- buildGraph ta t1 liveout ;;
   t2_live <- buildGraph ta t2 liveout ;;
   match topt with
   | None => livein <- extendClique t1_live t2_live ;; st_ex_return livein
   | Some t =>
     clashes <- st_ex_return (list.MAP ta (list.MAP fst (toAList t))) ;;
     cliqueInsertEdge clashes ;;
     st_ex_return clashes
   end
 | Seq t1 t2 => live <- buildGraph ta t2 liveout ;; buildGraph ta t1 live
 end.

Fixpoint extendGraph {A} (ta : A -> N) (edges : list (A*A)) : M arrayState unit state_exn :=
 match edges with
 | [] => st_ex_return tt
 | (x,y)::xs => insertEdge (ta x) (ta y) ;; extendGraph ta xs
 end.

Section GraphSimulation.
Variable base : ra_state.
Lemma sim_insert_edge x y : sim base (insert_edge x y) (insertEdge x y).
Proof.
 unfold insert_edge, insertEdge.
 apply sim_bind; [apply sim_read|]. intro adjx.
 apply sim_bind; [apply sim_read|]. intro adjy.
 rewrite !sortedInsert_exact. apply sim_ignore; apply sim_write.
Qed.
Lemma sim_list_insert_edge x l : sim base (list_insert_edge x l) (listInsertEdge x l).
Proof.
 induction l as [|y ys IH]; cbn [list_insert_edge listInsertEdge].
 - apply sim_return.
 - apply sim_ignore; [apply sim_insert_edge|exact IH].
Qed.
Lemma sim_clique_insert_edge l : sim base (clique_insert_edge l) (cliqueInsertEdge l).
Proof.
 induction l as [|x xs IH]; cbn [clique_insert_edge cliqueInsertEdge].
 - apply sim_return.
 - apply sim_ignore; [apply sim_list_insert_edge|exact IH].
Qed.
Lemma sim_extend_clique l : forall cli, sim base (extend_clique l cli) (extendClique l cli).
Proof.
 induction l as [|x xs IH]; intro cli; cbn [extend_clique extendClique].
 - apply sim_return.
 - destruct (list.MEM x cli); [apply IH|].
   apply sim_ignore; [apply sim_list_insert_edge|apply IH].
Qed.
Lemma sim_mk_graph ta ct : forall live, sim base (mk_graph ta ct live) (buildGraph ta ct live).
Proof.
 induction ct as [w r|t|topt t1 IH1 t2 IH2|t1 IH1 t2 IH2]; intro liveout; cbn [mk_graph buildGraph].
 - apply sim_bind; [apply sim_return|]. intro wta.
   apply sim_bind; [apply sim_return|]. intro rta.
   apply sim_bind; [apply sim_extend_clique|]. intro live.
   apply sim_bind; [apply sim_return|]. intro live'.
   apply sim_bind; [apply sim_extend_clique|]. intro livein. apply sim_return.
 - apply sim_bind; [apply sim_return|]. intro live.
   apply sim_ignore; [apply sim_clique_insert_edge|apply sim_return].
 - apply sim_bind; [apply IH1|]. intro live1.
   apply sim_bind; [apply IH2|]. intro live2.
   destruct topt as [t|].
   + apply sim_bind; [apply sim_return|]. intro clashes.
     apply sim_ignore; [apply sim_clique_insert_edge|apply sim_return].
   + apply sim_bind; [apply sim_extend_clique|]. intro livein. apply sim_return.
 - apply sim_bind; [apply IH2|]. intro live. apply IH1.
Qed.
Lemma sim_extend_graph {A} (ta : A -> N) edges :
 sim base (extend_graph ta edges) (extendGraph ta edges).
Proof.
 induction edges as [|[x y] xs IH]; cbn [extend_graph extendGraph].
 - apply sim_return.
 - apply sim_ignore; [apply sim_insert_edge|exact IH].
Qed.

End GraphSimulation.

Fixpoint decode_from (n : nat) (k : N) (t : num_map (list N)) : list (list N) :=
 match n with
 | O => []
 | S n => (match FastLookup.binary_lookup k t with Some x => x | None => [] end) :: decode_from n (k+1) t
 end.
Definition decode (a : arrayState) := decode_from (arrayLength a) 0 (arrayData a).
Lemma decode_from_eq xs : forall k t,
 (forall i, lookup (k+N.of_nat i) t = nth_error xs i) ->
 decode_from (List.length xs) k t = xs.
Proof.
 induction xs as [|x xs IH]; intros k t H; [reflexivity|].
 cbn [List.length decode_from].
 specialize (H O) as H0. cbn in H0. rewrite N.add_0_r in H0. rewrite FastLookup.binary_lookup_exact,H0.
 f_equal. apply IH. intro i. specialize (H (S i)).
 replace (k+1+N.of_nat i) with (k+N.of_nat (S i)) by lia.
 exact H.
Qed.
Lemma decode_represents xs a : represents xs a -> decode a = xs.
Proof.
 intros [Hlen Hnth]. unfold decode. rewrite <- Hlen. apply decode_from_eq.
 intro i. rewrite N.add_0_l, Hnth, Nat2N.id. reflexivity.
Qed.
Definition mk_graph_fast ta ct live (s : ra_state) : exc (list N) state_exn * ra_state :=
 let a := ArrayState (List.length (adj_ls s)) (encode (adj_ls s)) in
 let '(r,a') := buildGraph ta ct live a in (r,withAdj (decode a') s).
Theorem mk_graph_fast_exact ta ct live s : mk_graph_fast ta ct live s = mk_graph ta ct live s.
Proof.
 pose proof (sim_mk_graph s ta ct live s
   (ArrayState (List.length (adj_ls s)) (encode (adj_ls s)))) as H.
 assert (Hr : related s s (ArrayState (List.length (adj_ls s)) (encode (adj_ls s)))).
 { exists (adj_ls s). split; [symmetry; apply withAdj_self|apply represents_encode]. }
 specialize (H Hr). unfold mk_graph_fast.
 destruct (mk_graph ta ct live s) as [r s'] eqn:Es.
 destruct (buildGraph ta ct live (ArrayState (List.length (adj_ls s)) (encode (adj_ls s)))) as [r' a'] eqn:Ea.
 cbn [fst snd] in H. destruct H as [<- [xs [-> Hrep]]].
 rewrite (decode_represents xs a' Hrep). reflexivity.
Qed.

Definition extend_graph_fast {A} (ta : A -> N) edges (s : ra_state) : exc unit state_exn * ra_state :=
 let a := ArrayState (List.length (adj_ls s)) (encode (adj_ls s)) in
 let '(r,a') := extendGraph ta edges a in (r,withAdj (decode a') s).
Theorem extend_graph_fast_exact {A} (ta : A -> N) edges s :
 extend_graph_fast ta edges s = extend_graph ta edges s.
Proof.
 pose proof (sim_extend_graph s ta edges s
   (ArrayState (List.length (adj_ls s)) (encode (adj_ls s)))) as H.
 assert (Hr : related s s (ArrayState (List.length (adj_ls s)) (encode (adj_ls s)))).
 { exists (adj_ls s). split; [symmetry; apply withAdj_self|apply represents_encode]. }
 specialize (H Hr). unfold extend_graph_fast.
 destruct (extend_graph ta edges s) as [r s'] eqn:Es.
 destruct (extendGraph ta edges (ArrayState (List.length (adj_ls s)) (encode (adj_ls s)))) as [r' a'] eqn:Ea.
 cbn [fst snd] in H. destruct H as [<- [xs [-> Hrep]]].
 rewrite (decode_represents xs a' Hrep). reflexivity.
Qed.
