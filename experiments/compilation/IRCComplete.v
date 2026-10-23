(** Complete selection on function 87; use an explicit, suitably long timeout.
    The scalar observation avoids reading the full working graph back to a term. *)
From Galette Require Import Base.
From InitE.Compilation Require Import CompilerConfig Allocation Word0087_00Input Word0087_02Filter.
From InitE.Compilation Require SparseIRC.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
Time Eval vm_compute in
 match advance filtered (fun moves => SparseIRC.allocate_fast moves (snd heuristics) regs) with
 | (M_success stack,_) => Some (List.length stack)
 | _ => None
 end.
