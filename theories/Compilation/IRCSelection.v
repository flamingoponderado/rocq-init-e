(** Exact checkpoints within IRC selection. *)
From Galette Require Import Base.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From InitE.Compilation Require Import Allocation.
From InitE.Compilation Require SparseIRC.
Open Scope N_scope.
Definition initialize_selection moves k : RA N := fun s =>
 init_alloc1_heu moves (dim s) k s.
Theorem selection_phases {A} (r : exc A state_exn * ra_state)
 (moves : A -> list (N * (N*N))) scost k :
 advance r (fun v => do_alloc1 (moves v) scost k) =
 advance (advance (advance r (fun v => initialize_selection (moves v) k))
   (fun count => rpt_do_step scost k count)) (fun _ => get_stack).
Proof.
 destruct r as [[v|e] s]; cbn [advance]; [|reflexivity].
 unfold do_alloc1,initialize_selection,get_dim,get_stack,st_ex_bind,
 st_ex_ignore_bind,st_ex_return,advance.
 cbv beta iota zeta.
 destruct (init_alloc1_heu (moves v) (dim s) k s) as [[count|err] s1]; cbv beta iota zeta; try reflexivity.
Qed.

Definition do_alloc1_fast moves scost k := SparseIRC.allocate_fast moves scost k.
Theorem do_alloc1_fast_exact moves scost k s :
 do_alloc1_fast moves scost k s = do_alloc1 moves scost k s.
Proof. apply SparseIRC.allocate_fast_exact. Qed.
Theorem advance_do_alloc1_fast_exact {A} (r : exc A state_exn * ra_state)
 (moves : A -> list (N*(N*N))) scost k :
 advance r (fun v => do_alloc1_fast (moves v) scost k) =
 advance r (fun v => do_alloc1 (moves v) scost k).
Proof.
 destruct r as [[v|e] s]; cbn [advance]; [apply do_alloc1_fast_exact|reflexivity].
Qed.
