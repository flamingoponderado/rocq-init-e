(** State checkpoints for the monadic register allocator. *)
From Galette Require Import Base.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
Open Scope N_scope.
Definition advance {S A B E} (r : exc A E * S) (f : A -> M S B E) : exc B E * S :=
 match r with
 | (M_success v,s) => f v s
 | (M_failure e,s) => (M_failure e,s)
 end.
Definition initialState (n : N) : ra_state :=
 mk_ra_state (marray_replicate n []) (marray_replicate n Atemp)
 (marray_replicate n 0) n [] [] [] [] []
 (marray_replicate n 0) (marray_replicate n false) [].
Theorem allocator_phases alg scost k moves ct forced fs ta fa n :
 reg_alloc_aux alg scost k moves ct forced fs (ta,(fa,n)) =
 let moves0 := MAP (update_move (sp_default ta)) moves in
 let mvs := resort_moves (moves_to_sp moves0 LN) in
 let init := init_ra_state ct forced fs (ta,(fa,n)) (initialState n) in
 let filtered := advance init (fun _ => st_ex_FILTER (fun '(_, (x,y)) => full_consistency_ok k x y) moves0 []) in
 let allocated := advance filtered (fun moves => do_alloc1 (if bool_decide (alg = Simple) then [] else moves) scost k) in
 let assignedA := advance allocated (fun ls => assign_Atemps k ls (biased_pref mvs)) in
 let assignedS := advance assignedA (fun _ => assign_Stemps k (neg_biased_pref k mvs)) in
 fst (advance assignedS (fun _ => extract_color ta)).
Proof.
 unfold reg_alloc_aux, run_ira_state, do_reg_alloc, run, initialState.
 cbv beta iota zeta delta [FST SND fst snd ira_state_adj_ls ira_state_node_tag
 ira_state_degrees ira_state_dim ira_state_simp_wl ira_state_spill_wl
 ira_state_freeze_wl ira_state_avail_moves_wl ira_state_unavail_moves_wl
 ira_state_coalesced ira_state_move_related ira_state_stack].
 unfold st_ex_bind, st_ex_ignore_bind, st_ex_return, advance.
 cbv beta iota zeta.
 fold (initialState n).
 set (moves0 := MAP (update_move (sp_default ta)) moves).
 set (mvs := resort_moves (moves_to_sp moves0 LN)).
 destruct (init_ra_state ct forced fs (ta,(fa,n)) (initialState n)) as [[u|e] s1]; cbv beta iota zeta; try reflexivity.
 destruct (st_ex_FILTER (fun '(_, (x,y)) => full_consistency_ok k x y) moves0 [] s1) as [[mv|e] s2]; cbv beta iota zeta; try reflexivity.
 destruct (do_alloc1 (if bool_decide (alg = Simple) then [] else mv) scost k s2) as [[ls|e] s3]; cbv beta iota zeta; try reflexivity.
 destruct (assign_Atemps k ls (biased_pref mvs) s3) as [[u1|e] s4]; cbv beta iota zeta; try reflexivity.
 destruct (assign_Stemps k (neg_biased_pref k mvs) s4) as [[u2|e] s5]; cbv beta iota zeta; try reflexivity.
 destruct (extract_color ta s5) as [[col|e] s6]; reflexivity.
Qed.

Theorem initialization_phases ct forced fs ta fa n s :
 init_ra_state ct forced fs (ta,(fa,n)) s =
 advance (advance (mk_graph (sp_default ta) ct [] s)
 (fun _ => extend_graph (sp_default ta) forced))
 (fun _ => mk_tags n fs (sp_default fa)).
Proof.
 unfold init_ra_state, advance, st_ex_ignore_bind.
 cbv beta iota zeta.
 destruct (mk_graph (sp_default ta) ct [] s) as [[v|e] s1]; cbv beta iota zeta; try reflexivity.
Qed.
