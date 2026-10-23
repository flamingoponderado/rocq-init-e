(** Compare the same three original/sparse IRC steps and inspect thirty sparse
    steps. Build the generated function-87 initialization checkpoint first. *)
From Galette Require Import Base.
From InitE.Compilation Require Import CompilerConfig Word0087_00Input Word0087_03aHeuristics.
From InitE.Compilation Require SparseState SparseIRC.
From Galette.cakeml.compiler.backend.reg_alloc Require reg_alloc.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Stdlib Require Import List.
Import ListNotations.
Definition observe (s : reg_alloc.ra_state) :=
 [length (reg_alloc.simp_wl s); length (reg_alloc.spill_wl s);
  length (reg_alloc.freeze_wl s); length (reg_alloc.avail_moves_wl s);
  length (reg_alloc.unavail_moves_wl s); length (reg_alloc.stack s)].
Fixpoint originalSteps n s := observe s ::
 match n with O => [] | S n =>
 let '(ret,s') := reg_alloc.do_step (snd heuristics) regs s in
 match ret with M_success true => originalSteps n s' | _ => [observe s'] end end.
Fixpoint sparseSteps n f := observe (SparseState.original f) ::
 match n with O => [] | S n =>
 let '(ret,f') := SparseIRC.do_step (snd heuristics) regs f in
 match ret with M_success true => sparseSteps n f' | _ => [observe (SparseState.original f')] end end.
Time Eval vm_compute in originalSteps 3 (snd selectionInitialized).
Time Eval vm_compute in sparseSteps 3 (SparseState.pack (snd selectionInitialized)).
Time Eval vm_compute in sparseSteps 30 (SparseState.pack (snd selectionInitialized)).
