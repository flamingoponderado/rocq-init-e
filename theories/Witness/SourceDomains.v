(** Boolean deciders for the source memory domains of [SourceSemantics]. *)
From Galette Require Import Base.
From Stdlib Require Import Lia.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.cakeml.compiler.backend.proofs Require stack_removeProof.
From Galette.cakeml.pancake.proofs Require pan_globalsProof.
From InitE.InitE Require Import Parameters SourceSemantics.
Open Scope N_scope.

Definition ordinaryCount : N := (stackStart - sourceBase) / 8 - globalsWords.

Definition ordinaryDecider (w : word 64) : bool :=
  (sourceBase <=? w2n w) && ((w2n w - sourceBase) mod 8 =? 0) &&
  ((w2n w - sourceBase) / 8 <? ordinaryCount).

Definition sharedDecider (w : word 64) : bool :=
  aligned 3 w && (((inputStart <=? w2n w) && (w2n w <? inputEnd)) ||
                  ((outputStart <=? w2n w) && (w2n w <? outputEnd))).

Lemma bytes_in_word_64 : (bytes_in_word : word 64) = n2w 8.
Proof. reflexivity. Qed.

Lemma dimword_64 : dimword 64 = 18446744073709551616.
Proof. reflexivity. Qed.

Theorem ordinaryDecider_spec w : ordinaryDecider w = true <-> ordinaryDomain w.
Proof.
  unfold ordinaryDecider, ordinaryDomain.
  change (stack_removeProof.addresses (n2w sourceBase) ((stackStart - sourceBase) / 8 - globalsWords) w)
    with (w IN stack_removeProof.addresses (n2w sourceBase : word 64) ordinaryCount).
  rewrite pan_globalsProof.in_addresses, !Bool.andb_true_iff, N.leb_le, N.eqb_eq, N.ltb_lt.
  assert (Hw : w2n w < dimword 64) by apply w2n_lt.
  rewrite dimword_64 in Hw.
  assert (Hc : ordinaryCount = 3888119741) by reflexivity.
  cbv [sourceBase] in *; rewrite Hc.
  split.
  - intros [[Hle Hmod] Hlt]. exists ((w2n w - 2701131776) / 8). split; [|exact Hlt].
    apply word_eq_w2n.
    rewrite bytes_in_word_64, word_mul_n2w, word_add_n2w, w2n_n2w_small; rewrite ?dimword_64; lia.
  - intros (i & -> & Hi).
    rewrite bytes_in_word_64, word_mul_n2w, word_add_n2w, w2n_n2w_small; rewrite ?dimword_64; [|lia].
    replace (2701131776 + i * 8 - 2701131776) with (i * 8) by lia.
    rewrite N.Div0.mod_mul, N.div_mul by lia. lia.
Qed.

Theorem sharedDecider_spec w : sharedDecider w = true <-> sharedDomain w.
Proof.
  unfold sharedDecider, sharedDomain.
  rewrite Bool.andb_true_iff, Bool.orb_true_iff, !Bool.andb_true_iff, !N.leb_le, !N.ltb_lt.
  reflexivity.
Qed.
