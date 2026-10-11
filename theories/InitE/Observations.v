(** Original InitE/Observations.lean: replay, acceptance and reject classes. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics.ffi Require Import ffi.
From InitE.Guest Require Import GasLimit HostMemory.
From InitE.InitE Require Import Parameters SourceSemantics.
Open Scope N_scope.
Open Scope hol_string_scope.
Definition replayOracle {S : Type} (oc : oracle S) (initial : S)
 (events : list io_event) : S :=
 fold_left (fun host event =>
   match event with IO_event name configuration bytes =>
   match oc name host configuration (MAP fst bytes) with
   | Oracle_return next _ => next | Oracle_final _ => host
   end end) events initial.
Definition observedHost (input : InputBlob) (events : list io_event) : HostMemory :=
 replayOracle sourceOracle (guestHostMemory input) events.
Record OutputOffset := { offsetValue : N; offsetBound : offsetValue < 65536 }.
Definition outputByte (input : InputBlob) (events : list io_event)
 (offset : OutputOffset) : word8 :=
 match observedHost input events (n2w outputStart+n2w (offsetValue offset))%w with
 | Some value => value | None => n2w 0 end.
Definition normalHalt (out : outcome) : Prop :=
 match out with
 | Success => True | Resource_limit_hit => False
 | FFI_outcome (Final_event name _ _ result) => name = ExtCall (strlit "halt") /\ result = FFI_failed
 end.
Definition coveredOutcome (out : outcome) : Prop :=
 match out with
 | Success => True | Resource_limit_hit => False
 | FFI_outcome (Final_event name configuration _ result) => result = FFI_failed /\
   (name <> ExtCall (strlit "trap") \/
    (LENGTH configuration <> 1 /\ LENGTH configuration <> 6 /\ LENGTH configuration <> 7))
 end.
Definition acceptanceOffset : OutputOffset.
Proof. refine {| offsetValue := 32 |}; vm_compute; reflexivity. Defined.
Definition acceptedOutput (input : InputBlob) (out : outcome) (events : list io_event) : Prop :=
 normalHalt out /\ outputByte input events acceptanceOffset = n2w 1.
Definition matchingResult (input : InputBlob) (sourceOutcome : outcome)
 (sourceEvents : list io_event) (targetOutcome : outcome) (targetEvents : list io_event) : Prop :=
 if classical_dec (acceptedOutput input sourceOutcome sourceEvents)
 then acceptedOutput input targetOutcome targetEvents /\ forall offset,
      outputByte input sourceEvents offset = outputByte input targetEvents offset
 else coveredOutcome targetOutcome /\ ~ acceptedOutput input targetOutcome targetEvents.
Theorem matchingResult_refl input out events :
 coveredOutcome out -> matchingResult input out events out events.
Proof.
 intros H; unfold matchingResult; destruct (classical_dec _) as [HA|HA];
 split; auto.
Qed.
