(** Exact sparse working state for the register allocator. *)
From Galette Require Import Base.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From InitE.Compilation Require MapArray.
From Stdlib Require Import List.
Import ListNotations.
Open Scope N_scope.
Record state := State {
 original : ra_state;
 adjacency : MapArray.array (list N);
 tags : MapArray.array (tag);
 degree : MapArray.array (N);
 parents : MapArray.array (N);
 moves : MapArray.array (bool)
}.
Definition IM A := M state A state_exn.
Record related (s : ra_state) (f : state) : Prop := Related {
 r_adjacency : MapArray.rep (adj_ls s) (adjacency f);
 r_tags : MapArray.rep (node_tag s) (tags f);
 r_degree : MapArray.rep (degrees s) (degree f);
 r_parents : MapArray.rep (coalesced s) (parents f);
 r_moves : MapArray.rep (move_related s) (moves f);
 r_dim : dim s = dim (original f);
 r_simp_wl : simp_wl s = simp_wl (original f);
 r_spill_wl : spill_wl s = spill_wl (original f);
 r_freeze_wl : freeze_wl s = freeze_wl (original f);
 r_avail_moves_wl : avail_moves_wl s = avail_moves_wl (original f);
 r_unavail_moves_wl : unavail_moves_wl s = unavail_moves_wl (original f);
 r_stack : stack s = stack (original f)
}.
Definition sim {A} (p : RA A) (q : IM A) := forall s f, related s f ->
 fst (p s) = fst (q f) /\ related (snd (p s)) (snd (q f)).
Lemma sim_return {A} (v : A) : sim (st_ex_return v) (st_ex_return v).
Proof. intros s f H; split; [reflexivity|exact H]. Qed.
Lemma sim_bind {A B} (p : RA A) (q : IM A) (f : A -> RA B) (g : A -> IM B) :
 sim p q -> (forall v, sim (f v) (g v)) -> sim (st_ex_bind p f) (st_ex_bind q g).
Proof.
 intros Hp Hf s f0 H. specialize (Hp s f0 H). unfold st_ex_bind.
 destruct (p s) as [r s1]; destruct (q f0) as [r' f1].
 cbn [fst snd] in Hp. destruct Hp as [<- Hr]. destruct r as [v|e].
 - apply Hf; exact Hr.
 - split; [reflexivity|exact Hr].
Qed.
Lemma sim_ignore {A B} (p : RA A) (q : IM A) (f : RA B) (g : IM B) :
 sim p q -> sim f g -> sim (st_ex_ignore_bind p f) (st_ex_ignore_bind q g).
Proof. intros Hp Hf; apply sim_bind with (f:=fun _ => f) (g:=fun _ => g); auto. Qed.
Definition read_array {A} (get : state -> MapArray.array A) i : IM A :=
 fun f => (MapArray.sub Subscript i (get f),f).
Definition write_array {A} (get : state -> MapArray.array A)
 (set : MapArray.array A -> state -> state) i v : IM unit := fun f =>
 match MapArray.update Subscript v i (get f) with
 | M_success a => (M_success tt,set a f)
 | M_failure e => (M_failure e,f)
 end.
Definition adj_ls_sub i : IM (list N) := read_array adjacency i.
Lemma sim_adj_ls_sub i : sim (reg_alloc.adj_ls_sub i) (adj_ls_sub i).
Proof.
 intros s f H. unfold reg_alloc.adj_ls_sub,adj_ls_sub,Marray_sub,read_array.
 rewrite (MapArray.sub_rep Subscript (adj_ls s) (adjacency f) i (r_adjacency s f H)).
 split; [reflexivity|exact H].
Qed.
Definition with_adjacency (a : MapArray.array (list N)) f := State (original f) a (tags f) (degree f) (parents f) (moves f).
Definition update_adj_ls i v : IM unit := write_array adjacency with_adjacency i v.
Lemma sim_update_adj_ls i v : sim (reg_alloc.update_adj_ls i v) (update_adj_ls i v).
Proof.
 intros s f H. unfold reg_alloc.update_adj_ls,update_adj_ls,Marray_update,write_array.
 pose proof (MapArray.update_rep Subscript v i (adj_ls s) (adjacency f) (r_adjacency s f H)) as Hu.
 destruct (Mupdate Subscript v i (adj_ls s)) as [xs|e];
 destruct (MapArray.update Subscript v i (adjacency f)) as [a|e'];
 cbn [MapArray.results] in Hu; try contradiction.
 - split; [reflexivity|]. destruct H as [H_adjacency H_tags H_degree H_parents H_moves H_dim H_simp_wl H_spill_wl H_freeze_wl H_avail_moves_wl H_unavail_moves_wl H_stack]. constructor;
   cbn [with_adjacency adj_ls node_tag degrees dim simp_wl spill_wl freeze_wl avail_moves_wl unavail_moves_wl coalesced move_related stack original adjacency tags degree parents moves]; assumption.
 - subst e'. split; [reflexivity|exact H].
Qed.
Definition node_tag_sub i : IM (tag) := read_array tags i.
Lemma sim_node_tag_sub i : sim (reg_alloc.node_tag_sub i) (node_tag_sub i).
Proof.
 intros s f H. unfold reg_alloc.node_tag_sub,node_tag_sub,Marray_sub,read_array.
 rewrite (MapArray.sub_rep Subscript (node_tag s) (tags f) i (r_tags s f H)).
 split; [reflexivity|exact H].
Qed.
Definition degrees_sub i : IM (N) := read_array degree i.
Lemma sim_degrees_sub i : sim (reg_alloc.degrees_sub i) (degrees_sub i).
Proof.
 intros s f H. unfold reg_alloc.degrees_sub,degrees_sub,Marray_sub,read_array.
 rewrite (MapArray.sub_rep Subscript (degrees s) (degree f) i (r_degree s f H)).
 split; [reflexivity|exact H].
Qed.
Definition with_degree (a : MapArray.array (N)) f := State (original f) (adjacency f) (tags f) a (parents f) (moves f).
Definition update_degrees i v : IM unit := write_array degree with_degree i v.
Lemma sim_update_degrees i v : sim (reg_alloc.update_degrees i v) (update_degrees i v).
Proof.
 intros s f H. unfold reg_alloc.update_degrees,update_degrees,Marray_update,write_array.
 pose proof (MapArray.update_rep Subscript v i (degrees s) (degree f) (r_degree s f H)) as Hu.
 destruct (Mupdate Subscript v i (degrees s)) as [xs|e];
 destruct (MapArray.update Subscript v i (degree f)) as [a|e'];
 cbn [MapArray.results] in Hu; try contradiction.
 - split; [reflexivity|]. destruct H as [H_adjacency H_tags H_degree H_parents H_moves H_dim H_simp_wl H_spill_wl H_freeze_wl H_avail_moves_wl H_unavail_moves_wl H_stack]. constructor;
   cbn [with_degree adj_ls node_tag degrees dim simp_wl spill_wl freeze_wl avail_moves_wl unavail_moves_wl coalesced move_related stack original adjacency tags degree parents moves]; assumption.
 - subst e'. split; [reflexivity|exact H].
Qed.
Definition coalesced_sub i : IM (N) := read_array parents i.
Lemma sim_coalesced_sub i : sim (reg_alloc.coalesced_sub i) (coalesced_sub i).
Proof.
 intros s f H. unfold reg_alloc.coalesced_sub,coalesced_sub,Marray_sub,read_array.
 rewrite (MapArray.sub_rep Subscript (coalesced s) (parents f) i (r_parents s f H)).
 split; [reflexivity|exact H].
Qed.
Definition with_parents (a : MapArray.array (N)) f := State (original f) (adjacency f) (tags f) (degree f) a (moves f).
Definition update_coalesced i v : IM unit := write_array parents with_parents i v.
Lemma sim_update_coalesced i v : sim (reg_alloc.update_coalesced i v) (update_coalesced i v).
Proof.
 intros s f H. unfold reg_alloc.update_coalesced,update_coalesced,Marray_update,write_array.
 pose proof (MapArray.update_rep Subscript v i (coalesced s) (parents f) (r_parents s f H)) as Hu.
 destruct (Mupdate Subscript v i (coalesced s)) as [xs|e];
 destruct (MapArray.update Subscript v i (parents f)) as [a|e'];
 cbn [MapArray.results] in Hu; try contradiction.
 - split; [reflexivity|]. destruct H as [H_adjacency H_tags H_degree H_parents H_moves H_dim H_simp_wl H_spill_wl H_freeze_wl H_avail_moves_wl H_unavail_moves_wl H_stack]. constructor;
   cbn [with_parents adj_ls node_tag degrees dim simp_wl spill_wl freeze_wl avail_moves_wl unavail_moves_wl coalesced move_related stack original adjacency tags degree parents moves]; assumption.
 - subst e'. split; [reflexivity|exact H].
Qed.
Definition move_related_sub i : IM (bool) := read_array moves i.
Lemma sim_move_related_sub i : sim (reg_alloc.move_related_sub i) (move_related_sub i).
Proof.
 intros s f H. unfold reg_alloc.move_related_sub,move_related_sub,Marray_sub,read_array.
 rewrite (MapArray.sub_rep Subscript (move_related s) (moves f) i (r_moves s f H)).
 split; [reflexivity|exact H].
Qed.
Definition with_moves (a : MapArray.array (bool)) f := State (original f) (adjacency f) (tags f) (degree f) (parents f) a.
Definition update_move_related i v : IM unit := write_array moves with_moves i v.
Lemma sim_update_move_related i v : sim (reg_alloc.update_move_related i v) (update_move_related i v).
Proof.
 intros s f H. unfold reg_alloc.update_move_related,update_move_related,Marray_update,write_array.
 pose proof (MapArray.update_rep Subscript v i (move_related s) (moves f) (r_moves s f H)) as Hu.
 destruct (Mupdate Subscript v i (move_related s)) as [xs|e];
 destruct (MapArray.update Subscript v i (moves f)) as [a|e'];
 cbn [MapArray.results] in Hu; try contradiction.
 - split; [reflexivity|]. destruct H as [H_adjacency H_tags H_degree H_parents H_moves H_dim H_simp_wl H_spill_wl H_freeze_wl H_avail_moves_wl H_unavail_moves_wl H_stack]. constructor;
   cbn [with_moves adj_ls node_tag degrees dim simp_wl spill_wl freeze_wl avail_moves_wl unavail_moves_wl coalesced move_related stack original adjacency tags degree parents moves]; assumption.
 - subst e'. split; [reflexivity|exact H].
Qed.
Definition get_dim : IM (N) := fun f => (M_success (dim (original f)),f).
Lemma sim_get_dim : sim reg_alloc.get_dim get_dim.
Proof.
 intros s f H. unfold reg_alloc.get_dim,get_dim. split; [|exact H].
 cbn [fst]. f_equal. exact (r_dim s f H).
Qed.
Definition get_simp_wl : IM (list N) := fun f => (M_success (simp_wl (original f)),f).
Lemma sim_get_simp_wl : sim reg_alloc.get_simp_wl get_simp_wl.
Proof.
 intros s f H. unfold reg_alloc.get_simp_wl,get_simp_wl. split; [|exact H].
 cbn [fst]. f_equal. exact (r_simp_wl s f H).
Qed.
Definition set_simp_wl xs : IM unit := fun f => (M_success tt,State (snd (reg_alloc.set_simp_wl (E:=state_exn) xs (original f))) (adjacency f) (tags f) (degree f) (parents f) (moves f)).
Lemma sim_set_simp_wl xs : sim (reg_alloc.set_simp_wl xs) (set_simp_wl xs).
Proof.
 intros s f H. unfold set_simp_wl,reg_alloc.set_simp_wl. split; [reflexivity|].
 destruct H as [H_adjacency H_tags H_degree H_parents H_moves H_dim H_simp_wl H_spill_wl H_freeze_wl H_avail_moves_wl H_unavail_moves_wl H_stack]. constructor; cbn [fst snd adj_ls node_tag degrees dim simp_wl spill_wl freeze_wl avail_moves_wl unavail_moves_wl coalesced move_related stack original adjacency tags degree parents moves]; auto.
Qed.
Definition get_spill_wl : IM (list N) := fun f => (M_success (spill_wl (original f)),f).
Lemma sim_get_spill_wl : sim reg_alloc.get_spill_wl get_spill_wl.
Proof.
 intros s f H. unfold reg_alloc.get_spill_wl,get_spill_wl. split; [|exact H].
 cbn [fst]. f_equal. exact (r_spill_wl s f H).
Qed.
Definition set_spill_wl xs : IM unit := fun f => (M_success tt,State (snd (reg_alloc.set_spill_wl (E:=state_exn) xs (original f))) (adjacency f) (tags f) (degree f) (parents f) (moves f)).
Lemma sim_set_spill_wl xs : sim (reg_alloc.set_spill_wl xs) (set_spill_wl xs).
Proof.
 intros s f H. unfold set_spill_wl,reg_alloc.set_spill_wl. split; [reflexivity|].
 destruct H as [H_adjacency H_tags H_degree H_parents H_moves H_dim H_simp_wl H_spill_wl H_freeze_wl H_avail_moves_wl H_unavail_moves_wl H_stack]. constructor; cbn [fst snd adj_ls node_tag degrees dim simp_wl spill_wl freeze_wl avail_moves_wl unavail_moves_wl coalesced move_related stack original adjacency tags degree parents moves]; auto.
Qed.
Definition get_freeze_wl : IM (list N) := fun f => (M_success (freeze_wl (original f)),f).
Lemma sim_get_freeze_wl : sim reg_alloc.get_freeze_wl get_freeze_wl.
Proof.
 intros s f H. unfold reg_alloc.get_freeze_wl,get_freeze_wl. split; [|exact H].
 cbn [fst]. f_equal. exact (r_freeze_wl s f H).
Qed.
Definition set_freeze_wl xs : IM unit := fun f => (M_success tt,State (snd (reg_alloc.set_freeze_wl (E:=state_exn) xs (original f))) (adjacency f) (tags f) (degree f) (parents f) (moves f)).
Lemma sim_set_freeze_wl xs : sim (reg_alloc.set_freeze_wl xs) (set_freeze_wl xs).
Proof.
 intros s f H. unfold set_freeze_wl,reg_alloc.set_freeze_wl. split; [reflexivity|].
 destruct H as [H_adjacency H_tags H_degree H_parents H_moves H_dim H_simp_wl H_spill_wl H_freeze_wl H_avail_moves_wl H_unavail_moves_wl H_stack]. constructor; cbn [fst snd adj_ls node_tag degrees dim simp_wl spill_wl freeze_wl avail_moves_wl unavail_moves_wl coalesced move_related stack original adjacency tags degree parents moves]; auto.
Qed.
Definition get_avail_moves_wl : IM (list (N*(N*N))) := fun f => (M_success (avail_moves_wl (original f)),f).
Lemma sim_get_avail_moves_wl : sim reg_alloc.get_avail_moves_wl get_avail_moves_wl.
Proof.
 intros s f H. unfold reg_alloc.get_avail_moves_wl,get_avail_moves_wl. split; [|exact H].
 cbn [fst]. f_equal. exact (r_avail_moves_wl s f H).
Qed.
Definition set_avail_moves_wl xs : IM unit := fun f => (M_success tt,State (snd (reg_alloc.set_avail_moves_wl (E:=state_exn) xs (original f))) (adjacency f) (tags f) (degree f) (parents f) (moves f)).
Lemma sim_set_avail_moves_wl xs : sim (reg_alloc.set_avail_moves_wl xs) (set_avail_moves_wl xs).
Proof.
 intros s f H. unfold set_avail_moves_wl,reg_alloc.set_avail_moves_wl. split; [reflexivity|].
 destruct H as [H_adjacency H_tags H_degree H_parents H_moves H_dim H_simp_wl H_spill_wl H_freeze_wl H_avail_moves_wl H_unavail_moves_wl H_stack]. constructor; cbn [fst snd adj_ls node_tag degrees dim simp_wl spill_wl freeze_wl avail_moves_wl unavail_moves_wl coalesced move_related stack original adjacency tags degree parents moves]; auto.
Qed.
Definition get_unavail_moves_wl : IM (list (N*(N*N))) := fun f => (M_success (unavail_moves_wl (original f)),f).
Lemma sim_get_unavail_moves_wl : sim reg_alloc.get_unavail_moves_wl get_unavail_moves_wl.
Proof.
 intros s f H. unfold reg_alloc.get_unavail_moves_wl,get_unavail_moves_wl. split; [|exact H].
 cbn [fst]. f_equal. exact (r_unavail_moves_wl s f H).
Qed.
Definition set_unavail_moves_wl xs : IM unit := fun f => (M_success tt,State (snd (reg_alloc.set_unavail_moves_wl (E:=state_exn) xs (original f))) (adjacency f) (tags f) (degree f) (parents f) (moves f)).
Lemma sim_set_unavail_moves_wl xs : sim (reg_alloc.set_unavail_moves_wl xs) (set_unavail_moves_wl xs).
Proof.
 intros s f H. unfold set_unavail_moves_wl,reg_alloc.set_unavail_moves_wl. split; [reflexivity|].
 destruct H as [H_adjacency H_tags H_degree H_parents H_moves H_dim H_simp_wl H_spill_wl H_freeze_wl H_avail_moves_wl H_unavail_moves_wl H_stack]. constructor; cbn [fst snd adj_ls node_tag degrees dim simp_wl spill_wl freeze_wl avail_moves_wl unavail_moves_wl coalesced move_related stack original adjacency tags degree parents moves]; auto.
Qed.
Definition get_stack : IM (list N) := fun f => (M_success (stack (original f)),f).
Lemma sim_get_stack : sim reg_alloc.get_stack get_stack.
Proof.
 intros s f H. unfold reg_alloc.get_stack,get_stack. split; [|exact H].
 cbn [fst]. f_equal. exact (r_stack s f H).
Qed.
Definition set_stack xs : IM unit := fun f => (M_success tt,State (snd (reg_alloc.set_stack (E:=state_exn) xs (original f))) (adjacency f) (tags f) (degree f) (parents f) (moves f)).
Lemma sim_set_stack xs : sim (reg_alloc.set_stack xs) (set_stack xs).
Proof.
 intros s f H. unfold set_stack,reg_alloc.set_stack. split; [reflexivity|].
 destruct H as [H_adjacency H_tags H_degree H_parents H_moves H_dim H_simp_wl H_spill_wl H_freeze_wl H_avail_moves_wl H_unavail_moves_wl H_stack]. constructor; cbn [fst snd adj_ls node_tag degrees dim simp_wl spill_wl freeze_wl avail_moves_wl unavail_moves_wl coalesced move_related stack original adjacency tags degree parents moves]; auto.
Qed.
Definition pack s := State s (MapArray.encode (adj_ls s)) (MapArray.encode (node_tag s)) (MapArray.encode (degrees s)) (MapArray.encode (coalesced s)) (MapArray.encode (move_related s)).
Lemma pack_related s : related s (pack s).
Proof. constructor; try apply MapArray.encode_rep; reflexivity. Qed.
Definition unpack f := mk_ra_state (MapArray.decode ([]) (adjacency f)) (MapArray.decode (Atemp) (tags f)) (MapArray.decode (0) (degree f)) (dim (original f)) (simp_wl (original f)) (spill_wl (original f)) (freeze_wl (original f)) (avail_moves_wl (original f)) (unavail_moves_wl (original f)) (MapArray.decode (0) (parents f)) (MapArray.decode (false) (moves f)) (stack (original f)).
Lemma unpack_related s f : related s f -> unpack f = s.
Proof.
 intros [H_adjacency H_tags H_degree H_parents H_moves H_dim H_simp_wl H_spill_wl H_freeze_wl H_avail_moves_wl H_unavail_moves_wl H_stack]. unfold unpack.
 rewrite (MapArray.decode_rep ([]) (adj_ls s) (adjacency f) H_adjacency).
 rewrite (MapArray.decode_rep (Atemp) (node_tag s) (tags f) H_tags).
 rewrite (MapArray.decode_rep (0) (degrees s) (degree f) H_degree).
 rewrite (MapArray.decode_rep (0) (coalesced s) (parents f) H_parents).
 rewrite (MapArray.decode_rep (false) (move_related s) (moves f) H_moves).
 rewrite <- H_dim, <- H_simp_wl, <- H_spill_wl, <- H_freeze_wl, <- H_avail_moves_wl, <- H_unavail_moves_wl, <- H_stack.
 destruct s; reflexivity.
Qed.
Definition execute {A} (q : IM A) (s : ra_state) :=
 let '(r,f) := q (pack s) in (r,unpack f).
Theorem execute_exact {A} (p : RA A) (q : IM A) : sim p q -> forall s, execute q s = p s.
Proof.
 intros H s. specialize (H s (pack s) (pack_related s)). unfold execute.
 destruct (p s) as [r s1]; destruct (q (pack s)) as [r' f1].
 cbn [fst snd] in H. destruct H as [<- Hr]. rewrite (unpack_related s1 f1 Hr). reflexivity.
Qed.
