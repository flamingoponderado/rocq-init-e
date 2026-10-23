From Galette Require Import Base.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

Lemma map_replace_middle {A B} (f : A -> B) xs i x y :
  List.nth_error xs i = Some x ->
  f x = y ->
  List.map f xs =
    List.map f (List.firstn i xs) ++
    y :: List.map f (List.skipn (S i) xs).
Proof.
  intros Hnth Hxy.
  rewrite <- (List.firstn_skipn_middle i xs Hnth) at 1.
  rewrite List.map_app.
  cbn [List.map].
  now rewrite Hxy.
Qed.

Fixpoint chunk_at {A} (i : nat) (xs : list A) : list A :=
  match i with
  | O => List.firstn 8 xs
  | S j => chunk_at j (List.skipn 8 xs)
  end.

Definition gather {A B} (n : nat) (f : A -> B) (xs : list A) : list B :=
  List.concat
    (List.map (fun i => List.map f (chunk_at i xs)) (List.seq 0 n)).

Lemma gather_succ {A B} n (f : A -> B) xs :
  gather (S n) f xs =
  List.map f (List.firstn 8 xs) ++ gather n f (List.skipn 8 xs).
Proof.
  unfold gather at 1.
  cbn [List.seq List.map List.concat].
  rewrite <- List.seq_shift.
  rewrite List.map_map.
  reflexivity.
Qed.

Lemma gather_exact {A B} n (f : A -> B) xs :
  List.length xs <= 8 * n ->
  gather n f xs = List.map f xs.
Proof.
  revert xs.
  induction n as [|n IH]; intros xs Hlen.
  - destruct xs; cbn in Hlen; [reflexivity|lia].
  - rewrite gather_succ.
    rewrite IH.
    + rewrite <- List.map_app.
      now rewrite List.firstn_skipn.
    + rewrite List.length_skipn; lia.
Qed.
