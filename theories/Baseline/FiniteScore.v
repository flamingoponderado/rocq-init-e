(** A finite score exists for every infinity certificate.

    [Certificate] reads its input only through [guestHostMemory input]: the
    source run, the target's FFI state and initial memory, and the observed
    output all start from it. A host memory is a function
    [word 64 -> option word8], and functions between listable types take
    finitely many values, so the input-dependent step counts of an infinity
    certificate have a maximum. Divergent source runs are outside
    [Certificate], so they need no bound.

    The score is only shown to exist; nothing here computes it. *)
From Stdlib Require Import List NArith Lia FunctionalExtensionality Classical_Prop.
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.cakeml.semantics.ffi Require Import ffi.
From InitE.Guest Require Import Basic GasLimit HostMemory.
From InitE.InitE Require Import NatE SubmissionModel SourceSemantics Observations Challenge.
Open Scope N_scope.

Lemma finite_max {X : Type} (xs : list X) (Q : X -> N -> Prop)
 (Qmono : forall x k k', Q x k -> k <= k' -> Q x k') :
 (forall x, List.In x xs -> exists k, Q x k) -> exists k, forall x, List.In x xs -> Q x k.
Proof.
 induction xs as [|x xs IH]; intros H.
 - exists 0; intros _ [].
 - destruct (H x (or_introl eq_refl)) as [k1 H1].
   destruct IH as [k2 H2]; [intros y Hy; apply H; right; exact Hy|].
   exists (N.max k1 k2); intros y [<-|Hy].
   + apply (Qmono _ k1); [exact H1|lia].
   + apply (Qmono _ k2); [apply H2; exact Hy|lia].
Qed.

(** A monotone bound on each function of a listable function space is uniform. *)
Section FunctionSpace.
Context {A B : Type} (domain : list A) (codomain : list B)
 (domain_full : forall a, List.In a domain) (codomain_full : forall b, List.In b codomain)
 (P : (A -> B) -> N -> Prop)
 (mono : forall m k k', P m k -> k <= k' -> P m k')
 (pointwise : forall m, exists k, P m k).

Definition update (base : A -> B) (a : A) (b : B) : A -> B :=
 fun x => if classical_dec (x = a) then b else base x.

Lemma bounded_off_list (seen : list A) : forall base, exists k, forall m,
 (forall a, ~ List.In a seen -> m a = base a) -> P m k.
Proof.
 induction seen as [|a seen IH]; intros base.
 - destruct (pointwise base) as [k Hk]; exists k; intros m Hm.
   replace m with base; [exact Hk|].
   apply functional_extensionality; intros a; symmetry; apply Hm; intros [].
 - destruct (finite_max codomain (fun b k => forall m,
     (forall x, ~ List.In x seen -> m x = update base a b x) -> P m k)) as [k Hk].
   + intros b k k' H Hle m Hm; apply (mono m k); [apply H; exact Hm|exact Hle].
   + intros b _; apply IH.
   + exists k; intros m Hm; apply (Hk (m a) (codomain_full _)).
     intros x Hx; unfold update; destruct (classical_dec (x = a)) as [->|Hne]; [reflexivity|].
     apply Hm; intros [Heq|Hin]; [exact (Hne (eq_sym Heq))|exact (Hx Hin)].
Qed.

Theorem function_space_bound (base : A -> B) : exists k, forall m, P m k.
Proof.
 destruct (bounded_off_list domain base) as [k Hk]; exists k; intros m; apply Hk.
 intros a Ha; contradiction (Ha (domain_full a)).
Qed.
End FunctionSpace.

Definition allWords (n : N) : list (word n) :=
 List.map (fun i => n2w (N.of_nat i)) (List.seq 0 (N.to_nat (dimword n))).

Lemma allWords_full n (w : word n) : List.In w (allWords n).
Proof.
 unfold allWords; apply List.in_map_iff; exists (N.to_nat (w2n w)); split.
 - rewrite N2Nat.id; apply n2w_w2n.
 - apply List.in_seq; rewrite Nat.add_0_l; pose proof (w2n_lt w); lia.
Qed.

Lemma hostValues_full (v : option word8) : List.In v (None :: List.map Some (allWords 8)).
Proof.
 destruct v as [b|]; [right; apply List.in_map; apply allWords_full|left; reflexivity].
Qed.

Lemma sourceBehaviour_congr i j :
 guestHostMemory i = guestHostMemory j -> sourceBehaviour i = sourceBehaviour j.
Proof. intros same; unfold sourceBehaviour, sourceInitialState, sourceFfi; rewrite same; reflexivity. Qed.

Lemma matchingExecutionAt_congr s i j out events steps :
 guestHostMemory i = guestHostMemory j ->
 matchingExecutionAt s i out events steps -> matchingExecutionAt s j out events steps.
Proof.
 intros same; unfold matchingExecutionAt, initialState, initialMemory, sourceFfi,
  matchingResult, acceptedOutput, outputByte, observedHost; rewrite same; exact id.
Qed.

(** The same ROM and metadata with another score, as [VerificationCore] builds it. *)
Definition withScore (s : Submission) (k : NatE) : Submission :=
 Build_Submission (code s) k (anchorPc s) (names s) (first s) (extra s).

Lemma admitted_withScore s k : Admitted s -> Admitted (withScore s k).
Proof. destruct s; intros []; constructor; assumption. Qed.

Lemma matchingExecutionAt_withScore s k input out events steps :
 matchingExecutionAt s input out events steps ->
 matchingExecutionAt (withScore s k) input out events steps.
Proof. destruct s; exact id. Qed.

(** One step bound serves every covered input with the same host memory. *)
Definition BoundedAt (s : Submission) (memory : HostMemory) (k : N) : Prop :=
 forall input, guestHostMemory input = memory ->
 declaredGasLimit input <= 200000000 -> forall out events,
 sourceBehaviour input = Terminate out events -> coveredOutcome out ->
 exists steps, steps <= k /\ matchingExecutionAt s input out events steps.

Lemma boundedAt_exists s : Certificate s infinity -> forall memory, exists k, BoundedAt s memory k.
Proof.
 intros cert memory.
 destruct (classic (exists input out events, guestHostMemory input = memory /\
   declaredGasLimit input <= 200000000 /\ sourceBehaviour input = Terminate out events /\
   coveredOutcome out)) as [[i0 [o0 [e0 [V0 [G0 [S0 C0]]]]]]|none].
 - destruct (correct _ _ cert i0 G0 o0 e0 S0 C0) as [n [_ R]].
   exists n; intros input V G out events S C.
   assert (same : guestHostMemory i0 = guestHostMemory input) by congruence.
   assert (E : Terminate out events = Terminate o0 e0).
   { rewrite <- S, <- S0; apply sourceBehaviour_congr; symmetry; exact same. }
   injection E as -> ->.
   exists n; split; [lia|exact (matchingExecutionAt_congr s i0 input o0 e0 n same R)].
 - exists 0; intros input V G out events S C; exfalso; apply none.
   exists input, out, events; auto.
Qed.

Theorem finite_certificate_of_infinity s : Certificate s infinity ->
 exists bound, Certificate (withScore s (finite bound)) (finite bound).
Proof.
 intros cert.
 assert (mono : forall m k k', BoundedAt s m k -> k <= k' -> BoundedAt s m k').
 { intros m k k' H Hle input V G out events S C.
   destruct (H input V G out events S C) as [steps [Hs R]].
   exists steps; split; [lia|exact R]. }
 destruct (function_space_bound (allWords 64) (None :: List.map Some (allWords 8))
   (allWords_full 64) hostValues_full (BoundedAt s) mono (boundedAt_exists s cert)
   (fun (_ : word 64) => (None : option word8))) as [k Hk].
 exists k; constructor; [reflexivity|apply admitted_withScore, (admitted _ _ cert)|].
 intros input G out events S C.
 destruct (Hk (guestHostMemory input) input eq_refl G out events S C) as [steps [Hs R]].
 exists steps; split; [exact Hs|apply matchingExecutionAt_withScore; exact R].
Qed.
