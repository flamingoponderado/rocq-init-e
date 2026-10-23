From Galette Require Import Base.
From Stdlib Require Import List.

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
