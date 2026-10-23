(** Exact allocator evaluation with sparse-map graph initialization. *)
From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc linear_scan.
From Galette.cakeml.compiler.backend Require word_alloc.
From InitE.Compilation Require Import Allocation.
From InitE.Compilation Require FastGraph IRCSelection.
Open Scope N_scope.

Lemma advance_extend_graph_exact {A B} (r : exc A state_exn * ra_state) (ta : B -> N) edges :
 advance r (fun _ => FastGraph.extend_graph_fast ta edges) =
 advance r (fun _ => extend_graph ta edges).
Proof.
 destruct r as [[v|e] s]; cbn [advance]; [apply FastGraph.extend_graph_fast_exact|reflexivity].
Qed.

Definition initialize ct forced fs ta fa n s :=
 advance (advance (FastGraph.mk_graph_fast (sp_default ta) ct [] s)
 (fun _ => FastGraph.extend_graph_fast (sp_default ta) forced))
 (fun _ => mk_tags n fs (sp_default fa)).
Lemma initialize_exact ct forced fs ta fa n s :
 initialize ct forced fs ta fa n s = init_ra_state ct forced fs (ta,(fa,n)) s.
Proof.
 unfold initialize. rewrite FastGraph.mk_graph_fast_exact, advance_extend_graph_exact,
 initialization_phases. reflexivity.
Qed.

Definition reg_alloc_aux_fast alg scost k moves ct forced fs tfn :=
 let '(ta,(fa,n)) := tfn in
 let moves0 := MAP (update_move (sp_default ta)) moves in
 let mvs := resort_moves (moves_to_sp moves0 LN) in
 let init := initialize ct forced fs ta fa n (initialState n) in
 let filtered := advance init (fun _ => st_ex_FILTER (fun '(_, (x,y)) => full_consistency_ok k x y) moves0 []) in
 let allocated := advance filtered (fun moves => IRCSelection.do_alloc1_fast (if bool_decide (alg = Simple) then [] else moves) scost k) in
 let assignedA := advance allocated (fun ls => assign_Atemps k ls (biased_pref mvs)) in
 let assignedS := advance assignedA (fun _ => assign_Stemps k (neg_biased_pref k mvs)) in
 fst (advance assignedS (fun _ => extract_color ta)).
Theorem reg_alloc_aux_fast_exact alg scost k moves ct forced fs tfn :
 reg_alloc_aux_fast alg scost k moves ct forced fs tfn = reg_alloc_aux alg scost k moves ct forced fs tfn.
Proof.
 destruct tfn as [ta [fa n]]. unfold reg_alloc_aux_fast.
 rewrite allocator_phases, initialize_exact, IRCSelection.advance_do_alloc1_fast_exact. reflexivity.
Qed.
Definition reg_alloc_fast alg scost k moves ct forced fs :=
 reg_alloc_aux_fast alg scost k moves ct forced fs (mk_bij ct).
Theorem reg_alloc_fast_exact alg scost k moves ct forced fs :
 reg_alloc_fast alg scost k moves ct forced fs = reg_alloc alg scost k moves ct forced fs.
Proof. unfold reg_alloc_fast, reg_alloc. apply reg_alloc_aux_fast_exact. Qed.
Definition select_reg_alloc_fast alg spillcosts k heu_moves tree forced fs :=
 if 4 <=? alg then linear_scan_reg_alloc k heu_moves tree forced
 else reg_alloc_fast (if alg <=? 1 then Simple else IRC) spillcosts k heu_moves tree forced fs.
Theorem select_reg_alloc_fast_exact alg spillcosts k heu_moves tree forced fs :
 select_reg_alloc_fast alg spillcosts k heu_moves tree forced fs =
 word_alloc.select_reg_alloc alg spillcosts k heu_moves tree forced fs.
Proof.
 unfold select_reg_alloc_fast, word_alloc.select_reg_alloc.
 destruct (4 <=? alg); [reflexivity|apply reg_alloc_fast_exact].
Qed.
