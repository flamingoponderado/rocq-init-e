(** A resumable IRC loop. A zero remainder records early termination. *)
From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From InitE.Compilation Require Import Allocation.
From InitE.Compilation Require SparseIRC.
Open Scope N_scope.
Fixpoint chunk (steps : nat) scost k (remaining : N) : RA N :=
 match steps with
 | O => st_ex_return remaining
 | S n => if remaining =? 0 then st_ex_return 0 else
    st_ex_bind (do_step scost k) (fun again =>
      if again then chunk n scost k (remaining-1) else st_ex_return 0)
 end.
Lemma chunk_resume steps scost k : forall remaining s,
 advance (chunk steps scost k remaining s) (rpt_do_step scost k) =
 rpt_do_step scost k remaining s.
Proof.
 induction steps as [|n IH]; intros remaining s; [reflexivity|].
 cbn [chunk]. destruct (N.eqb_spec remaining 0) as [->|Hne].
 - rewrite (proj1 (rpt_do_step_def scost k 0)). reflexivity.
 - assert (Hr : rpt_do_step scost k remaining =
      st_ex_bind (do_step scost k) (fun b => if b then rpt_do_step scost k (remaining-1) else st_ex_return tt)).
   { replace remaining with (N.succ (remaining-1)) at 1 by lia.
     exact (proj2 (rpt_do_step_def scost k (remaining-1))). }
   rewrite Hr.
   unfold st_ex_bind at 1 2.
   destruct (do_step scost k s) as [[again|err] next]; cbn [advance].
   + destruct again; [apply IH|].
     cbn [st_ex_return advance]. rewrite (proj1 (rpt_do_step_def scost k 0)). reflexivity.
   + reflexivity.
Qed.
Fixpoint chunk_fast (steps : nat) scost k (remaining : N) : SparseState.IM N :=
 match steps with
 | O => st_ex_return remaining
 | S n => if remaining =? 0 then st_ex_return 0 else
    st_ex_bind (SparseIRC.do_step scost k) (fun again =>
      if again then chunk_fast n scost k (remaining-1) else st_ex_return 0)
 end.
Lemma chunk_sim steps scost k : forall remaining,
 SparseState.sim (chunk steps scost k remaining) (chunk_fast steps scost k remaining).
Proof.
 induction steps as [|n IH]; intro remaining; cbn [chunk chunk_fast].
 - apply SparseState.sim_return.
 - destruct (remaining =? 0); [apply SparseState.sim_return|].
   apply SparseState.sim_bind; [apply SparseIRC.sim_do_step|].
   intro again; destruct again; [apply IH|apply SparseState.sim_return].
Qed.
Definition run steps scost k remaining := SparseState.execute (chunk_fast steps scost k remaining).
Lemma run_exact steps scost k remaining s : run steps scost k remaining s = chunk steps scost k remaining s.
Proof. apply SparseState.execute_exact. apply chunk_sim. Qed.
Lemma checkpoint_resume steps scost k (r : exc N state_exn * ra_state) :
 advance r (rpt_do_step scost k) =
 advance (advance r (run steps scost k)) (rpt_do_step scost k).
Proof.
 destruct r as [[remaining|err] s]; cbn [advance]; [|reflexivity].
 rewrite run_exact. symmetry. apply chunk_resume.
Qed.
