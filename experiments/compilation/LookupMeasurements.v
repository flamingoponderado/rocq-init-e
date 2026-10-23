(** Isolate lookup cost; both sweeps must return the same sum. *)
From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.list.src Require Import list rich_list.
From InitE.Compilation Require FastLookup.
Open Scope N_scope.
Definition table := Eval vm_compute in fromList (COUNT_LIST 6420).
Definition keys := Eval vm_compute in COUNT_LIST 6420.
Definition sweep (get : N -> num_map N -> option N) :=
 List.fold_left (fun acc i => match get i table with Some n => acc+n | None => acc end) keys 0.
Time Eval vm_compute in sweep (@lookup N).
Time Eval vm_compute in sweep (@FastLookup.binary_lookup N).
Time Eval vm_compute in sweep (@FastLookup.binary_lookup N).
Time Eval vm_compute in sweep (@lookup N).
Time Eval vm_compute in sweep (@FastLookup.binary_lookup N).
Time Eval vm_compute in sweep (@lookup N).
